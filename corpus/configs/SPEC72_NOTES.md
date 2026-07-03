# Spec 72 (EWD998_anim) — CLOSED

**Corpus-file-format finding:** `data/tla_files/72.tla` is not a bare module — upstream
ships it with an embedded `---- CONFIG EWD998_anim ----` cfg block *before* the
`---- MODULE ----` block (a valid Toolbox convention TLC's `-config file.tla` flag
can parse directly from the combined file, but our harness expects exactly one module
per `.tla` file and the cfg supplied separately). Extracted the module portion to
`corpus/configs/patches/72.tla` and reproduced the embedded cfg (minus the unsupported
`ALIAS` stanza, `corpus/configs/ALIAS_CFG.md`) as `corpus/configs/overrides/72.cfg`.

This unblocked SANY and got TLC into real `Init` computation, but exposed three further
issues, all root-caused and fixed this session (re-verification/grinding pass):

## Bug 1 — `AnimSpec`'s `Init!5` picked the wrong (redundant) conjunct, missing two real ones

`EWD998ChanID`'s own `Init` (corpus spec 74, byte-identical upstream) has exactly six
top-level conjuncts in this order: `1 clock, 2 counter, 3 inbox, 4 active, 5 color,
6 passes` (counted directly from the source). `AnimSpec` explicitly restates
`active`/`color`/`counter`/`inbox` itself (deliberately different values for animation
purposes), then adds a single `/\ Init!5` — the 5th conjunct, `color`, already
redundantly covered. Both `clock` (1) and `passes` (6) — the two conjuncts genuinely
*not* covered by AnimSpec's own restatements — were never referenced at all, leaving
both completely unconstrained: `Error: current state is not a legal state`, with
`clock = null` and `passes = null` in the reported initial state. Fixed: replaced the
single wrong `Init!5` with `Init!1` (clock) and `Init!6` (passes) — the two conjuncts
actually missing.

## Bug 2 — the same conjunct's custom `inbox` token record was missing a `vc` field

Once bug 1 was fixed, TLC advanced further and failed differently: `Attempted to select
nonexistent field "vc" from the record [color |-> "black", q |-> 0, type |-> "tok"]`.
`AnimSpec`'s own hand-built `inbox` initializer constructs a token record with only
`type`/`q`/`color`, but `EWD998ChanID`'s `Receive`/`InitiateProbe` actions read
`inbox[n][j].vc` (the message's vector-clock payload) unconditionally on any token
message. `EWD998ChanID`'s own `Init` puts `vc |-> clock[n]` on its token; `AnimSpec`'s
override simply forgot this field. Fixed: added `vc |-> clock[n]` to match.

## Bug 3 — `Init!1` needed reordering before the conjunct that reads `clock[n]`

Fixing bug 2 introduced `clock[n]` fixed inside the `inbox` conjunct, which is
textually *before* `Init!1` (which binds `clock`) in `AnimSpec`'s conjunct list. TLC
binds `Init`'s variables in written order — a later conjunct can't be read by an
earlier one in the same `Init`, even though logically they're just simultaneous
constraints. Fixed: moved `/\ Init!1` to the front of `AnimSpec`, before any conjunct
that uses `clock`.

## Bug 4 (config, not code) — `CHECK_DEADLOCK` needed to be `FALSE`

With all three above fixed, TLC ran to a clean, complete, exhaustive exploration (15
states, 13 distinct, 0 left on queue) and then reported `fail_deadlock` — but this is
the *expected* end of a legitimately-terminating protocol run: EWD998's termination
detection genuinely reaches a quiescent state where no more `System(n)` actions are
enabled once the token confirms termination, and `AnimSpec`'s own comment says its
purpose is to "generate traces for large numbers of nodes" for animation, not to
exhaustively check deadlock-freedom. Same `CHECK_DEADLOCK FALSE` idiom already used for
this family's other terminating-algorithm specs (73, 79). Added to
`corpus/configs/overrides/72.cfg`.

**Result:** `sany=pass, tlc=pass`, non-vacuous, exhaustive (15 states generated, 0 left
on queue). All four fixes verified live via the harness, not assumed — each bug's exact
error message quoted above was reproduced before being fixed, one at a time.

All four defects are byte-identical upstream (this exact animation spec, never run
through TLC there either — a `.cfg` embedded in the `.tla` file for Toolbox convenience,
but nothing in `tla-examples`'s own CI/test infrastructure exercises it).
