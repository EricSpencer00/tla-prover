#!/usr/bin/env python3
"""Resolve candidate arXiv IDs against the real arXiv API. Anything that
doesn't resolve gets reported so it can be dropped rather than guessed at."""
import json, sys, time, urllib.request, urllib.parse
import xml.etree.ElementTree as ET

IDS = """
2607.25333 2602.12058 2606.05792 2607.23425 2606.06133 2501.03073 2512.09758
2509.23130 2604.12172 2602.23389 2205.06360 2211.07216 2109.11987 2404.18048
2606.02019 2602.08384
2604.05820 2509.22908 2602.18307 2501.06283 2505.23135 2512.10173 2509.25197
2508.02733 2605.26457 2306.15626 2407.10040 2511.03108 2508.15878 2606.12594
2606.19315 2505.03171 2605.30914 2412.06512 2602.11481
2505.23486 2508.04440 2607.13303 2607.13292 2507.08665 2410.10135 2511.11816
2502.00963
2410.02089 2402.03300 2305.18290 2504.11343 2308.01825 2203.14465 2203.02155
2606.06260 2605.31058 2603.24202 2402.00658
2106.09685 2405.09673 2404.15159 2601.04823 2604.26340 2607.21978 2504.21190
2502.15828 2507.00029 2412.16216 2603.12577 2603.02224 2512.17720 2510.13003
2402.12220 2402.15415
2509.07430 2604.16027 2602.07464 2607.04733 2605.00365 2601.12401
2604.15149 2510.00915 2606.01066
2502.06215 2605.24079 2605.19999 2406.13990 2502.00678 2512.10218 2507.11059
2505.20411 2506.17208 2406.06443 2504.13416 2506.14474 2506.15271 2509.05449
2508.07054 2310.16789 2404.02936 2202.07646 2311.04850 2311.09783 2312.16337
2308.08493 2404.18824 2403.07974 2403.04811 2502.14425
2510.01631 2503.14023 2410.01720 2409.12993 2510.23208 2603.23562
2303.17651 2508.00083 2505.02931 2405.17057 2607.05810 2306.09896 2107.03374
2601.19334 2510.27055
""".split()

NS = {"a": "http://www.w3.org/2005/Atom"}
out, missing = {}, []

for i in range(0, len(IDS), 25):
    batch = IDS[i:i + 25]
    url = ("http://export.arxiv.org/api/query?id_list="
           + ",".join(batch) + "&max_results=50")
    try:
        raw = urllib.request.urlopen(url, timeout=60).read()
    except Exception as e:
        print(f"batch {i} FAILED: {e}", file=sys.stderr)
        time.sleep(5)
        continue
    root = ET.fromstring(raw)
    for entry in root.findall("a:entry", NS):
        aid_url = entry.findtext("a:id", "", NS)
        aid = aid_url.rsplit("/", 1)[-1]
        base = aid.split("v")[0]
        title = " ".join((entry.findtext("a:title", "", NS) or "").split())
        if not title or title.lower() == "error":
            continue
        authors = [a.findtext("a:name", "", NS)
                   for a in entry.findall("a:author", NS)]
        cats = [c.get("term") for c in entry.findall("a:category", NS)]
        out[base] = {
            "arxiv_id": base,
            "version": aid,
            "title": title,
            "authors": authors,
            "published": entry.findtext("a:published", "", NS)[:10],
            "updated": entry.findtext("a:updated", "", NS)[:10],
            "categories": cats,
            "comment": " ".join((entry.findtext(
                "{http://arxiv.org/schemas/atom}comment", "") or "").split()),
            "abstract": " ".join((entry.findtext("a:summary", "", NS) or "").split()),
        }
    time.sleep(3)

for x in IDS:
    if x not in out:
        missing.append(x)

print(f"resolved {len(out)} / {len(IDS)}")
print("MISSING:", " ".join(missing))
json.dump(out, open(sys.argv[1], "w"), indent=1)
