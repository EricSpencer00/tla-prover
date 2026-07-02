# Mutation kill-rate (W0.4) — first pass

`harness/mutation.py`: `python3 -m harness.mutation --specs <comma-list> [--extra-cfg-dir corpus/configs/drafts] [--timeout N]`

**Scope, stated plainly:** whole-module regex operator swaps, one mutation operator
per mutant, not single-point localized mutation (a full SpecGen-style tool mutates one
operator *occurrence* per mutant and tracks each independently — real future work, not
done here).

## What's in the set

- `and_to_or`: every `/\` → `\/`. Safe everywhere — `/\`/`\/` are unambiguously the
  boolean connectives in TLA+, no syntactic collision.
- `plus_to_minus`: ` + ` → ` - ` in arithmetic contexts (regex-bounded by digit/space/
  paren neighbors). Safe in principle; untested on a spec that actually contains a
  bare ` + ` in the tested run (all 5 sample specs below had zero matches — noted
  honestly as `"applied": false`, not silently skipped).

## What got tried and dropped

`eq_to_neq` (`=`→`#`) and `lt_to_le` (`<`→`<=`), even after excluding `==`, `<=`,
`>=`, `:=`. Reason: `=` is *also* the required token in `EXCEPT ![i] = v` clause syntax
(not a boolean comparison there) and inside `=>` (implication) — a regex has no way to
tell those apart from a real `x = y` comparison without actually parsing the
expression. Confirmed by testing on spec 38 (CoffeeCan): the mutation turned
`can' = [can EXCEPT !.black = @ - 1]` into invalid syntax (`can' # [can EXCEPT
!.black # @ - 1]`) and `THEOREM Spec =>` into `THEOREM Spec #>`, both SANY parse
failures on every real spec tried. Whole-file regex mutation cannot safely cover
relational operators for arbitrary TLA+; doing this correctly needs a real parser
(tree-sitter-tlaplus, or SANY's own AST) — not attempted here.

## Sample run (5 clean-passing specs from draftfix-final)

`python3 -m harness.mutation --specs 38,5,45,102,67 --timeout 30 --extra-cfg-dir corpus/configs/drafts`

| spec | module | and_to_or | plus_to_minus | kill_rate |
|------|--------|-----------|----------------|-----------|
| 38  | CoffeeCan     | killed (tlc=error)  | not applicable (no match) | 1.0 |
| 5   | ACP_SB        | killed (tlc=error)  | not applicable            | 1.0 |
| 45  | DijkstraMutex | killed (tlc=error)  | not applicable            | 1.0 |
| 102 | KeyValueStore | killed (tlc=error)  | not applicable            | 1.0 |
| 67  | EWD840_proof  | **survived** (tlc=pass) | not applicable         | **0.0** |

**Real finding, not a harness artifact:** spec 67's and_to_or mutant still passes TLC
cleanly — every `/\` in the module became `\/` and TLC still reports no error. This is
exactly the antidote-to-vacuous-100%-claims signal ROADMAP.md calls for: EWD840_proof's
TLC-checkable slice (it's a `proof_module`, TLC is a secondary check per Amendment 1,
TLAPS is its real criterion — already 65/65 obligations proved, see
`corpus/configs/TLAPS_REPORT.md`) doesn't distinguish this specific mutation from the
original. Not root-caused further here — worth another look before treating spec 67's
TLC "clean" line as meaningful on its own (its TLAPS result already carries the real
weight for this spec under Amendment 1).

## Not done (no silent caps)

Only run on 5 specs as a validation sample, not the full corpus. A full pass — every
spec that gets a clean, non-vacuous TLC result — would apply both mutations and record
kill_rate in the results ledger per spec. Not run here for time; the harness command
above is ready to do it (`python3 -m harness run`'s ledger doesn't yet call this
automatically — wiring `mutation.py` into `run_sweep()` as an opt-in stage is the next
step, not done in this pass).
