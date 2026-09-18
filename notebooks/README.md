# TLA-Prover lab

Create an isolated environment and open the lab from the repository root:

```bash
python3 -m venv .venv-tlakit
.venv-tlakit/bin/python -m pip install -r notebooks/requirements.txt
.venv-tlakit/bin/python -m tlakit.kernel.install --user
.venv-tlakit/bin/jupyter lab notebooks/tla_prover_lab.ipynb
```

The notebook uses TLAKit's public runner for its harmless smoke check.  Polaris
and Sophia are separate backends: their cells make non-interactive, read-only
probes and never submit a scheduler job.  Private TLAKit service endpoints can
be supplied through `TLAKIT_POLARIS_ENDPOINT` and `TLAKIT_SOPHIA_ENDPOINT`;
SSH aliases can be overridden with `TLAKIT_POLARIS_SSH` and
`TLAKIT_SOPHIA_SSH`.

No cluster reachability, training loss, or text-skill score counts as a prover
result.  Promotion still requires a strict improvement on the frozen protected
gate with genuine SANY/proof evidence.
