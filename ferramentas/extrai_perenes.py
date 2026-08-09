"""Extrai os talhoes de culturas PERENES (cafe, citrus/laranja, outras) do
raster MapBiomas 2023 e recorta para GO+DF.

Processa por faixas horizontais (o raster inteiro nao cabe na memoria);
um talhao cortado na emenda vira dois poligonos vizinhos — visualmente
identico e a area se conserva."""
import json, math, sqlite3, sys
import numpy as np, rasterio
from rasterio import features as rfeat
from rasterio.windows import Window

SCR = "/private/tmp/claude-501/-Users-vantuiroliveira/28434ddf-db7f-4446-8247-d7a005bcaf72/scratchpad"
R = "/Users/vantuiroliveira/atlas-agro/mapbiomas_goias_2023.tif"
CLASSES = {46: "Café", 47: "Laranja / citrus", 48: "Outras perenes"}
MIN_HA = 1.0

src = rasterio.open(R)
FAIXA = 2048
brutos = []
for topo in range(0, src.height, FAIXA):
    alt = min(FAIXA, src.height - topo)
    win = Window(0, topo, src.width, alt)
    arr = src.read(1, window=win)
    tr = src.window_transform(win)
    for k in CLASSES:
        m = (arr == k)
        if not m.any():
            continue
        for geom, val in rfeat.shapes(m.astype(np.uint8), mask=m, transform=tr,
                                      connectivity=8):
            anel = geom["coordinates"][0]
            if len(anel) < 4:
                continue
            lat0 = sum(p[1] for p in anel) / len(anel)
            kx = math.cos(math.radians(lat0))
            s = 0.0
            for i in range(len(anel) - 1):
                x1, y1 = anel[i][0] * kx * 111320, anel[i][1] * 110574
                x2, y2 = anel[i + 1][0] * kx * 111320, anel[i + 1][1] * 110574
                s += x1 * y2 - x2 * y1
            ha = abs(s) / 2 / 10000
            if ha < MIN_HA:
                continue
            brutos.append({"cl": k, "ha": round(ha, 2), "anel": anel})
    print(f"  faixa {topo}: acumulado {len(brutos):,} talhoes", flush=True)
src.close()
print(f"talhoes brutos (>= {MIN_HA} ha): {len(brutos):,}", flush=True)

# --- recorte GO+DF: centroide dentro de algum municipio do Atlas ---
con = sqlite3.connect(SCR + "/dtv_df/atlas.db")
con.row_factory = sqlite3.Row
muns = []
for r in con.execute("""SELECT c.municipio_id, m.nome, c.geojson
                        FROM municipio_contorno c JOIN municipios m ON m.id = c.municipio_id"""):
    try:
        aneis = json.loads(r["geojson"])
    except Exception:
        continue
    xs = [p[0] for a in aneis for p in a]; ys = [p[1] for a in aneis for p in a]
    muns.append({"id": r["municipio_id"], "nome": r["nome"], "aneis": aneis,
                 "bb": (min(xs), min(ys), max(xs), max(ys))})

def dentro(x, y, anel):
    d, n = False, len(anel); j = n - 1
    for i in range(n):
        xi, yi = anel[i]; xj, yj = anel[j]
        if (yi > y) != (yj > y) and x < (xj - xi) * (y - yi) / ((yj - yi) or 1e-12) + xi:
            d = not d
        j = i
    return d

saida = []
for b in brutos:
    cx = sum(p[0] for p in b["anel"]) / len(b["anel"])
    cy = sum(p[1] for p in b["anel"]) / len(b["anel"])
    mid = None
    for m in muns:
        bb = m["bb"]
        if not (bb[0] <= cx <= bb[2] and bb[1] <= cy <= bb[3]):
            continue
        if any(dentro(cx, cy, a) for a in m["aneis"]):
            mid = m["id"]
            break
    if mid is None:
        continue          # fora de GO+DF (cerrado mineiro etc.)
    saida.append({**b, "mun": mid, "cx": round(cx, 5), "cy": round(cy, 5)})
print(f"dentro de GO+DF: {len(saida):,}", flush=True)
from collections import Counter
por_cl = Counter()
area_cl = Counter()
for s_ in saida:
    por_cl[s_["cl"]] += 1
    area_cl[s_["cl"]] += s_["ha"]
for k, n in por_cl.items():
    print(f"  {CLASSES[k]:<18}{n:>6,} talhoes  {area_cl[k]:>10,.0f} ha", flush=True)
json.dump(saida, open(SCR + "/perenes_go.json", "w"))
