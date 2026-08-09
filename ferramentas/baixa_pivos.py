"""Baixa os pivos centrais de Goias e do Distrito Federal do portal de dados
abertos da ANA. Duas armadilhas do servico, as duas ja custaram caro aqui:
 1) supportsPagination=false — paginar por offset devolve sempre a MESMA pagina;
    e preciso avancar pelo proprio FID;
 2) a base nao e uma lista de pivos: e um LEVANTAMENTO COMPLETO por ano
    (1985..2019), e o mesmo pivo reaparece em cada ano em que existia — ate 7
    vezes. Sem juntar, o mapa empilha circulos e a area irrigada quadruplica.
Guarda um registro por pivo: o levantamento mais recente + desde quando existe."""
import json, gzip, math, time, urllib.parse, urllib.request
from collections import defaultdict

U = ("https://www.snirh.gov.br/arcgis/rest/services/SPR/"
     "Irrigada_por_Pivos_Mapiados/FeatureServer/0/query")
ESTADOS = ["Goiás", "Distrito Federal"]
SAI = "/Users/vantuiroliveira/chatwoot-crm/pivos.json.gz"


def pede(params):
    for tent in range(5):
        try:
            with urllib.request.urlopen(U + "?" + urllib.parse.urlencode(params),
                                        timeout=180) as r:
                return json.loads(r.read().decode("utf-8"))
        except Exception as e:
            print("  retry", tent, e, flush=True)
            time.sleep(4)
    raise SystemExit("servico da ANA nao respondeu")


brutos = []
for uf in ESTADOS:
    ultimo, vistos = -1, set()
    while True:
        d = pede({"where": "NM_ESTADO='%s' AND FID > %d" % (uf, ultimo),
                  "outFields": "FID,HECTARES,CD_GEOCMU,ANO",
                  "returnCentroid": "true", "returnGeometry": "false",
                  "resultRecordCount": 1000, "orderByFields": "FID",
                  "outSR": 4326, "f": "json"})
        fs = d.get("features") or []
        if not fs:
            break
        for f in fs:
            c, a = f.get("centroid") or {}, f["attributes"]
            fid = a["FID"]
            ultimo = max(ultimo, fid)
            if fid in vistos or c.get("x") is None:
                continue
            vistos.add(fid)
            brutos.append({"lng": round(c["x"], 5), "lat": round(c["y"], 5),
                           "ha": round(a.get("HECTARES") or 0, 1),
                           "ibge": a.get("CD_GEOCMU") or "",
                           "ano": (a.get("ANO") or "")[:4]})
        print(f"  {uf}: {len(vistos):,} registros", flush=True)
        if len(fs) < 1000:
            break

print(f"total bruto: {len(brutos):,} registros", flush=True)


def raio(ha):
    return math.sqrt(max(ha, 0.1) * 10000 / math.pi)


def dist(a, b):
    dy = (a["lat"] - b["lat"]) * 111320
    dx = (a["lng"] - b["lng"]) * 111320 * math.cos(math.radians(a["lat"]))
    return math.hypot(dx, dy)


CEL = 0.01
grade = defaultdict(list)
for i, p in enumerate(brutos):
    grade[(int(p["lat"] / CEL), int(p["lng"] / CEL))].append(i)
pai = list(range(len(brutos)))


def acha(x):
    while pai[x] != x:
        pai[x] = pai[pai[x]]
        x = pai[x]
    return x


for (cy, cx), idxs in grade.items():
    viz = []
    for dy in (-1, 0, 1):
        for dx in (-1, 0, 1):
            viz += grade.get((cy + dy, cx + dx), [])
    for i in idxs:
        for j in viz:
            if j <= i:
                continue
            lim = max(0.40 * min(raio(brutos[i]["ha"]), raio(brutos[j]["ha"])), 60)
            if dist(brutos[i], brutos[j]) <= lim:
                ra, rb = acha(i), acha(j)
                if ra != rb:
                    pai[rb] = ra

grupos = defaultdict(list)
for i in range(len(brutos)):
    grupos[acha(i)].append(i)

ultimo_lev = max(p["ano"] for p in brutos)
saida = []
for g in grupos.values():
    regs = sorted((brutos[i] for i in g), key=lambda x: x["ano"])
    u = regs[-1]
    saida.append([u["lng"], u["lat"], u["ha"], u["ibge"], u["ano"], regs[0]["ano"]])
saida.sort(key=lambda x: -x[2])
with gzip.open(SAI, "wt", encoding="utf-8") as g:
    json.dump({"fonte": "ANA - Levantamento da Agricultura Irrigada por Pivos Centrais",
               "uf": "GO+DF", "ultimo_levantamento": ultimo_lev,
               "observacao": ("um registro por pivo: a ANA publica um levantamento completo "
                              "por ano e o mesmo pivo se repete em cada um"),
               "campos": ["lng", "lat", "ha", "ibge", "ano", "desde"],
               "pivos": saida}, g, ensure_ascii=False, separators=(",", ":"))
print(f"{len(brutos):,} registros -> {len(saida):,} pivos distintos", flush=True)
print(f"area irrigada: {sum(p[2] for p in saida):,.0f} ha", flush=True)
