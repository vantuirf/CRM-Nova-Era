"""Baixa os imoveis rurais do Distrito Federal do GeoServer publico do SICAR.

Por que nao pelo site do CAR: la o download por estado exige captcha. O
GeoServer (geoserver.car.gov.br) publica as MESMAS camadas por WFS aberto,
sem captcha — e e a fonte oficial.

Guarda um .jsonl: uma linha por imovel, com o codigo CAR, area, municipio,
status e os aneis do contorno em [lon,lat]."""
import json, time, urllib.parse, urllib.request

B = "https://geoserver.car.gov.br/geoserver/sicar/ows"
SAI = "/private/tmp/claude-501/-Users-vantuiroliveira/28434ddf-db7f-4446-8247-d7a005bcaf72/scratchpad/car_df.jsonl"
PASSO = 500


def pede(inicio):
    p = {"service": "WFS", "version": "2.0.0", "request": "GetFeature",
         "typeNames": "sicar:sicar_imoveis_df", "count": PASSO,
         "startIndex": inicio, "sortBy": "cod_imovel",
         "outputFormat": "application/json", "srsName": "EPSG:4326"}
    for tent in range(5):
        try:
            with urllib.request.urlopen(B + "?" + urllib.parse.urlencode(p), timeout=300) as r:
                return json.loads(r.read().decode("utf-8"))
        except Exception as e:
            print("  retry", tent, e, flush=True)
            time.sleep(5)
    raise SystemExit("GeoServer do CAR nao respondeu em startIndex=%d" % inicio)


n, inicio = 0, 0
with open(SAI, "w", encoding="utf-8") as f:
    while True:
        d = pede(inicio)
        fs = d.get("features") or []
        if not fs:
            break
        for x in fs:
            p, g = x["properties"], x.get("geometry")
            if not g:
                continue
            if str(p.get("status_imovel") or "") in ("CA", "SU"):
                continue   # cancelado/suspenso: registro morto ou travado,
                           # terra contada em dobro (pedido do usuario)
            # MultiPolygon -> lista de aneis externos; Polygon -> um so
            aneis = []
            if g["type"] == "MultiPolygon":
                for poly in g["coordinates"]:
                    if poly:
                        aneis.append(poly[0])
            elif g["type"] == "Polygon" and g["coordinates"]:
                aneis.append(g["coordinates"][0])
            if not aneis:
                continue
            f.write(json.dumps({
                "car": p.get("cod_imovel"), "area": p.get("area"),
                "municipio": p.get("municipio"), "ibge": p.get("cod_municipio_ibge"),
                "status": p.get("status_imovel"), "condicao": p.get("condicao"),
                "tipo": p.get("tipo_imovel"), "aneis": aneis}, ensure_ascii=False) + "\n")
            n += 1
        print(f"  {n:,} imoveis", flush=True)
        if len(fs) < PASSO:
            break
        inicio += PASSO
print("total:", n, flush=True)
