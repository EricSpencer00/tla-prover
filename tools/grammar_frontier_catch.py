"""Grammar catch rate on the FRONTIER specs, not the whole corpus.

tools/grammar_falsereject.py answers "is this grammar safe" (false rejects on
known-good specs) over every spec we have. That global number does not predict
what a decode-time grammar does for the 5 specs that actually block the
staircase (55, 121, 135, 141, 148), and the full run is slow enough to be
unusable -- its per-reject diagnosis walks one character at a time.

This asks the narrower question A5 needs: of the parse-failing candidates these
5 specs actually produced, how many does the grammar reject? Sampled per spec
(seed 0) so it finishes in about a minute.

  tools/smoke/e2e/.venv/bin/python -u tools/grammar_frontier_catch.py [N_PER_SPEC]

CAVEAT, do not drop it when quoting the number: this measures rejection of text
the model DID emit. Under constrained decoding those tokens are unreachable, so
the model emits something else, which may or may not parse. The result is the
share of observed bad output the constraint blocks, not a predicted gain.
"""
import json,sys,time,random
from pathlib import Path
sys.path.insert(0,"tools")
from grammar_falsereject import make_checker, module_region
from collections import Counter, defaultdict
FRONT={"55","121","135","141","148"}
acc=make_checker(Path("harness/grammars/tla_module_v1.ebnf").read_text())
cands=defaultdict(list); seen=set()
for run in Path("results/runs").iterdir():
    rp=run/"rows.jsonl"
    if not rp.is_file() or run.name.startswith(("QUARANTINE","smoke","drytest","lewm")): continue
    for ln in rp.read_text(errors="replace").splitlines():
        try: x=json.loads(ln)
        except Exception: continue
        s=str(x.get("spec"))
        if s not in FRONT or str(x.get("sany")) not in ("fail","fail_missing_module"): continue
        smp=x.get("sample")
        if smp is None or str(smp)=="corruption": continue
        k=(run.name,s,str(smp))
        if k in seen: continue
        seen.add(k)
        cp=x.get("candidate_path"); lp=x.get("log_path")
        if not cp or not lp: continue
        c=run/cp; L=Path(lp)
        if not L.is_absolute(): L=run/lp
        if not (c.is_file() and L.is_file()): continue
        if "Could not parse module" not in L.read_text(errors="replace"): continue
        cands[s].append(c)
random.seed(0)
N=int(sys.argv[1]) if len(sys.argv)>1 else 25
print(f"parse-failing candidates available: {{k:len(v) for k,v in sorted(cands.items())}}", flush=True)
tot=Counter(); rej=Counter()
t0=time.time()
for s in sorted(cands,key=int):
    smp=random.sample(cands[s], min(N,len(cands[s])))
    for c in smp:
        txt=module_region(c.read_text(errors="replace"))
        tot[s]+=1
        if not acc(txt): rej[s]+=1
    print(f"  spec {s}: grammar rejects {rej[s]}/{tot[s]} = {rej[s]/max(tot[s],1):.0%}   ({time.time()-t0:.0f}s)", flush=True)
T=sum(tot.values()); R=sum(rej.values())
print(f"FRONTIER catch rate on parse failures: {R}/{T} = {R/max(T,1):.1%}")
