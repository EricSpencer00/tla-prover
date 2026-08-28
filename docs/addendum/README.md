# TLA-Prover addendum

Build:

    tectonic -X compile main.tex

Regenerate every number and figure from the ledgers before building:

    python3 collect_data.py     # re-scores results/runs/* -> data.json
    python3 figures.py          # data.json -> figures/*.pdf (+ .png twins)

`data.json` is the single source for the tables and figures. Nothing numeric is
typed into the LaTeX by hand, so a stale number cannot survive a re-run.
`FACTS.md` is the prose brief the sections were written against; it and
`data.json` must agree.

Class files, bibliography, and preamble are copied from the parent paper so the
two documents typeset identically.
