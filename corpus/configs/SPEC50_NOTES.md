# Spec 50 (Synod) — deeper analysis, still not attempted

Full structure: `Synod` (outer module, `VARIABLES input, output`) contains a **nested**
TLA+ module `Inner` (`VARIABLES allInput, chosen`; nested modules share the enclosing
module's declarations by block position, not `EXTENDS`) defining `IInit`/`IChoose`/
`IFail`/`INext`/`ISpec`. After `Inner` closes, still inside `Synod`:

```
IS(chosen, allInput) == INSTANCE Inner
SynodSpec == \EE chosen, allInput : IS(chosen, allInput)!ISpec
```

`\EE` is temporal existential quantification — a refinement-mapping construct for
theorem proving, not something TLC can model-check directly. This is why no upstream
wrapper exists for bare `Synod` (confirmed by the original research pass): `SynodSpec`
itself is fundamentally not a TLC-checkable formula, and `HDiskSynod`/`DiskSynod`
(specs 47/48, closed this session) only exercise `Synod`'s inherited `Ballot`/
`IsMajority` operators, never `SynodSpec`.

**Possible path, not attempted:** `IS(chosen, allInput)!ISpec` for *fixed* (not
existentially hidden) `chosen`/`allInput` — treating them as ordinary state variables
of a larger system rather than refinement witnesses — would be model-checkable in
principle: a wrapper extending `Synod`, declaring `VARIABLES chosen, allInput`, with
`MCInit == IS(chosen, allInput)!IInit` and `MCNext == IS(chosen, allInput)!INext`. This
is TLA+'s "state-variable-parameterized instance" pattern (the instance's parameters
are themselves the enclosing spec's own primed/unprimed state), which is a real and
used technique — but getting the parameterization right (does `IS(chosen, allInput)`
correctly track `chosen'`/`allInput'` through the `INSTANCE` boundary, or does it need
re-instantiating each step?) is subtle enough that a wrong attempt could produce a
wrapper that *runs* and *passes* while checking something other than the intended
semantics — worse than an honest "not attempted." Not implemented this pass; would
need either deeper TLA+ semantics verification against the actual TLC output (e.g.
confirm the state space matches hand-traced expectations) or independent review before
trusting a "pass" here.
