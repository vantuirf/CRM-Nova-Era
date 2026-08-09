"""Atualiza pivos.json.gz com o levantamento de 2022 da ANA (Boletim SNIRH 4).

O arquivo atual tem a serie 1985-2019 ja deduplicada (um registro por pivo,
com "desde"). O 2022 entra como levantamento mais recente:
 - pivo de 2022 que casa com um existente (centros a menos de 40% do menor
   raio) herda o "desde" e passa a ano=2022 com a area de 2022;
 - pivo de 2022 sem par e NOVO: desde=2022 (e a resposta ao usuario — o que
   ele viu na imagem e nao estava marcado);
 - pivo antigo que NAO aparece em 2022 mantem o ultimo ano dele e vira o
   cinza tracejado ("pode estar desativado")."""
import gzip, json, math, shapefile
from collections import defaultdict

SCR = "/private/tmp/claude-501/-Users-vantuiroliveira/28434ddf-db7f-4446-8247-d7a005bcaf72/scratchpad"
ATUAL = "/Users/vantuiroliveira/chatwoot-crm/pivos.json.gz"

velhos = json.load(gzip.open(ATUAL, "rt", encoding="utf-8"))["pivos"]
print(f"base atual (ate 2019): {len(velhos):,} pivos")

sf = shapefile.Reader(SCR + "/pivos2022/ANA_PivosCentrais_2022_BR_env")
campos = [f[0] for f in sf.fields[1:]]
i_ha, i_cd, i_uf = campos.index("Hectares"), campos.index("MUNIC_CD"), campos.index("UF")
novos22 = []
for k in range(sf.numRecords):
    r = sf.record(k)
    if r[i_uf] not in ("GO", "DF"):
        continue
    s = sf.shape(k)
    pts = s.points
    lng = sum(p[0] for p in pts) / len(pts)
    lat = sum(p[1] for p in pts) / len(pts)
    novos22.append({"lng": round(lng, 5), "lat": round(lat, 5),
                    "ha": round(float(r[i_ha] or 0), 1), "ibge": str(r[i_cd] or "")})
print(f"levantamento 2022 em GO+DF: {len(novos22):,} pivos")


def raio(ha):
    return math.sqrt(max(ha, 0.1) * 10000 / math.pi)


def dist(a, b):
    dy = (a["lat"] - b["lat"]) * 111320
    dx = (a["lng"] - b["lng"]) * 111320 * math.cos(math.radians(a["lat"]))
    return math.hypot(dx, dy)


# grade dos antigos para casamento rapido
CEL = 0.01
grade = defaultdict(list)
antigos = [{"lng": p[0], "lat": p[1], "ha": p[2], "ibge": p[3], "ano": p[4], "desde": p[5]}
           for p in velhos]
for i, p in enumerate(antigos):
    grade[(int(p["lat"] / CEL), int(p["lng"] / CEL))].append(i)

usados = set()
saida, novos_de_verdade = [], 0
for n in novos22:
    cy, cx = int(n["lat"] / CEL), int(n["lng"] / CEL)
    cands = []
    for dy in (-1, 0, 1):
        for dx in (-1, 0, 1):
            cands += grade.get((cy + dy, cx + dx), [])
    par, menor = None, 1e18
    for i in cands:
        if i in usados:
            continue
        d = dist(n, antigos[i])
        if d <= max(0.40 * min(raio(n["ha"]), raio(antigos[i]["ha"])), 60) and d < menor:
            par, menor = i, d
    if par is not None:
        usados.add(par)
        a = antigos[par]
        saida.append([n["lng"], n["lat"], n["ha"], n["ibge"] or a["ibge"], "2022", a["desde"]])
    else:
        novos_de_verdade += 1
        saida.append([n["lng"], n["lat"], n["ha"], n["ibge"], "2022", "2022"])

# 2a passada: pivo que mudou de tamanho/desenho desloca o centro e escapa do
# limiar justo. Um "novo" com um "sumido" colado (ate 80% do MAIOR raio) e o
# MESMO pivo reformado: herda o desde e nao vira par fantasma novo+sumido.
sobras = [i for i in range(len(antigos)) if i not in usados]
recasados = 0
for s_ in saida:
    if s_[5] != "2022":
        continue
    melhor, menor = None, 1e18
    for i in sobras:
        a2 = antigos[i]
        d2 = dist({"lng": s_[0], "lat": s_[1]}, a2)
        if d2 <= 0.8 * max(raio(s_[2]), raio(a2["ha"])) and d2 < menor:
            melhor, menor = i, d2
    if melhor is not None:
        usados.add(melhor)
        sobras.remove(melhor)
        s_[5] = antigos[melhor]["desde"]
        recasados += 1
print(f"  recasados na 2a passada (pivo reformado): {recasados}")

sumidos = 0
for i, a in enumerate(antigos):
    if i not in usados:
        sumidos += 1
        saida.append([a["lng"], a["lat"], a["ha"], a["ibge"], a["ano"], a["desde"]])

# 3a passada: o criterio final do arquivo e NUNCA ter dois pivos empilhados
# (regra dos testes: centros a menos de 40% do menor raio, min 60 m). Se um
# pivo de 2022 ficou em cima de um antigo nao casado, e o mesmo pivo
# reequipado: o antigo e absorvido (o 2022 herda o desde mais antigo).
grade2 = defaultdict(list)
for i, x in enumerate(saida):
    grade2[(int(x[1] / CEL), int(x[0] / CEL))].append(i)
tirar = set()
for (cy, cx), idxs in grade2.items():
    viz = []
    for dy in (-1, 0, 1):
        for dx in (-1, 0, 1):
            viz += grade2.get((cy + dy, cx + dx), [])
    for i in idxs:
        if i in tirar:
            continue
        for j in viz:
            if j <= i or j in tirar:
                continue
            a_, b_ = saida[i], saida[j]
            dd = dist({"lng": a_[0], "lat": a_[1]}, {"lng": b_[0], "lat": b_[1]})
            if dd <= max(0.40 * min(raio(a_[2]), raio(b_[2])), 60):
                fica, sai = (i, j) if (a_[4], a_[2]) >= (b_[4], b_[2]) else (j, i)
                # herda o desde mais antigo dos dois
                saida[fica][5] = min(saida[fica][5], saida[sai][5])
                tirar.add(sai)
if tirar:
    print(f"  absorvidos na 3a passada (empilhados): {len(tirar)}")
    saida = [x for i, x in enumerate(saida) if i not in tirar]

saida.sort(key=lambda x: -x[2])
with gzip.open(ATUAL, "wt", encoding="utf-8") as g:
    json.dump({"fonte": "ANA - Levantamento da Agricultura Irrigada por Pivos Centrais "
                        "(serie 1985-2019 + Boletim SNIRH 4, mascara de 2022)",
               "uf": "GO+DF", "ultimo_levantamento": "2022",
               "observacao": ("um registro por pivo: cada ano da ANA e um levantamento "
                              "completo e o mesmo pivo se repete em cada um"),
               "campos": ["lng", "lat", "ha", "ibge", "ano", "desde"],
               "pivos": saida}, g, ensure_ascii=False, separators=(",", ":"))
print(f"\nRESULTADO: {len(saida):,} pivos no arquivo")
print(f"  vistos em 2022:        {len(novos22):,}")
novos_finais = sum(1 for x in saida if x[4]=="2022" and x[5]=="2022")
print(f"  NOVOS desde 2019:      {novos_finais:,}  <- o que o usuario viu sem marcacao")
print(f"  sumiram (nao em 2022): {sumidos:,}")
print(f"  area 2022: {sum(p[2] for p in saida if p[4]=='2022'):,.0f} ha")
