"""Baixa do IBGE (PAM 2023, tabela 5457 do SIDRA) a area plantada oficial de
Laranja e Cafe por municipio de GO e DF.

Motivo: o MapBiomas subconta perenes fora do cinturao de SP — Itaberai tem
1.309 ha de laranja no IBGE e o satelite viu ~150 ha. O usuario pegou o erro."""
import gzip, json, time, urllib.request

PRODUTOS = {"40151": "Laranja", "40139": "Café"}
SAIDA = "/Users/vantuiroliveira/chatwoot-crm/pam.json.gz"


def pede(uf):
    u = ("https://apisidra.ibge.gov.br/values/t/5457/n6/in%20n3%20" + uf +
         "/v/8331/p/last/c782/" + ",".join(PRODUTOS) + "?formato=json")
    for tent in range(4):
        try:
            with urllib.request.urlopen(u, timeout=180) as r:
                return json.loads(r.read().decode("utf-8"))
        except Exception as e:
            print("  retry", tent, e, flush=True)
            time.sleep(4)
    raise SystemExit("SIDRA nao respondeu")


itens = []
dados_ano = []
for uf in ("52", "53"):
    dados = pede(uf)
    for r in dados[1:]:
        v = r.get("V")
        if v in ("-", "...", "..", None, "X"):
            continue
        itens.append([r["D1C"], PRODUTOS.get(r["D4C"], r["D4N"]), float(v)])
        if r["D3N"] not in dados_ano:
            dados_ano.append(r["D3N"])
    print(f"  UF {uf}: acumulado {len(itens)} linhas", flush=True)

with gzip.open(SAIDA, "wt", encoding="utf-8") as g:
    json.dump({"fonte": "IBGE - Producao Agricola Municipal 2023 (SIDRA t5457, v8331 area plantada)",
               "ano": dados_ano[0] if dados_ano else "?", "campos": ["ibge", "cultura", "area_ha"],
               "itens": itens}, g, ensure_ascii=False, separators=(",", ":"))
print("total:", len(itens), flush=True)
for c in ("Laranja", "Café"):
    tot = sum(i[2] for i in itens if i[1] == c)
    print(f"  {c}: {tot:,.0f} ha em GO+DF", flush=True)
