"""Build a portable, oracle-free dependency bundle for protected holdout eval."""
import argparse, hashlib, json, shutil
from pathlib import Path

def sha(b): return hashlib.sha256(b).hexdigest()

def main(a):
    packet = json.loads(a.packet.read_bytes())
    out = a.output.resolve()
    if out.exists(): raise ValueError('append-only output already exists')
    files = {}
    for row in packet['tasks']:
        metas = [row['source'], *({'path':p,'sha256':h} for p,h in row['dependencies'].items()),
                 *({'path':p,'sha256':h} for p,h in row['wrapper_dependencies'].items())]
        if row.get('wrapper'): metas.append(row['wrapper'])
        for meta in metas:
            p = Path(meta['path']); raw = p.read_bytes()
            if sha(raw) != meta['sha256']: raise ValueError(f'hash mismatch: {p}')
            files[meta['sha256']] = str(p)
    out.mkdir(parents=True); (out/'files').mkdir()
    for h, source in sorted(files.items()): shutil.copyfile(source, out/'files'/f'{h}.tla')
    (out/'packet.json').write_bytes(a.packet.read_bytes())
    (out/'manifest.json').write_text(json.dumps({'sha256_to_source':files,'count':len(files)},indent=2)+'\n')
    print(json.dumps({'tasks':len(packet['tasks']),'files':len(files),'output':str(out)}))

if __name__ == '__main__':
    p=argparse.ArgumentParser(); p.add_argument('--packet',type=Path,required=True); p.add_argument('--output',type=Path,required=True); main(p.parse_args())
