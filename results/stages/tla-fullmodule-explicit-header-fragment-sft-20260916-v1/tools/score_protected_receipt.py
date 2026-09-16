import json, sys, time
from pathlib import Path
from harness import runner

receipt = json.loads(Path(sys.argv[1]).read_text())
out = Path(sys.argv[2]); out.mkdir(parents=True, exist_ok=False)
rows=[]
for i, rec in enumerate(receipt['records']):
    text=rec['raw_reply']
    module=runner.module_name(text)
    work=out/'checks'/f"{i:02d}-{rec['row']}-{rec['arm']}-{rec['generation']}"
    work.mkdir(parents=True)
    path=work/f'{module or "candidate"}.tla'; path.write_text(text)
    started=time.time(); status, log, _=runner.check_sany(path, work, 30)
    (work/'sany.log').write_text(log or '')
    rows.append({'index':i,'row':rec['row'],'arm':rec['arm'],'generation':rec['generation'],
                 'module':module,'sany':status,'elapsed_seconds':time.time()-started,
                 'log':str(work/'sany.log')})
summary={'schema':1,'kind':'protected_paired_sany_score','source_receipt':str(Path(sys.argv[1]).resolve()),
 'packet_sha256':receipt['packet_sha256'],'grammar_sha256':receipt['grammar_sha256'],
 'prompt_intervention':receipt.get('prompt_intervention'),'records':len(rows),'rows':rows}
for arm in receipt['arms']:
    x=[r for r in rows if r['arm']==arm]; summary[arm]={'pass':sum(r['sany']=='pass' for r in x),'fail':sum(r['sany']!='pass' for r in x),'n':len(x)}
summary['overall']={'pass':sum(r['sany']=='pass' for r in rows),'fail':sum(r['sany']!='pass' for r in rows),'n':len(rows)}
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
