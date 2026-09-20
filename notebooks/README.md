# TLA-Prover lab

Create an isolated environment and open the lab from the repository root:

```bash
python3 -m venv .venv-tlakit
.venv-tlakit/bin/python -m pip install -r notebooks/requirements.txt
.venv-tlakit/bin/python -m ipykernel install --user --name tla-prover --display-name "TLA-Prover (Python)"
.venv-tlakit/bin/jupyter lab notebooks/tla_prover_lab.ipynb
```

The notebook is the live inspection surface for teammates. It includes the
run lifecycle, an explicit model × training-method matrix, TLAKit's harmless
smoke check, a local evidence-ledger scan, and non-interactive Polaris/Sophia
probes. The cluster cells show only user-owned process metadata and never
submit, cancel, or promote a scheduler job.

Private TLAKit service endpoints can be supplied through
`TLAKIT_POLARIS_ENDPOINT` and `TLAKIT_SOPHIA_ENDPOINT`; SSH aliases can be
overridden with `TLAKIT_POLARIS_SSH` and `TLAKIT_SOPHIA_SSH`.

No cluster reachability, training loss, or text-skill score counts as a prover
result.  Promotion still requires a strict improvement on the frozen protected
gate with genuine SANY/proof evidence.
