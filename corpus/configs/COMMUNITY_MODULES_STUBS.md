# Community Modules are stub/placeholder for anything needing real Java behavior

`tools/community-modules/*.tla` (vendored from `tools/CommunityModules-deps.jar`,
`tools/TOOLS.md`) are declaration-only `.tla` files. Several operators in them —
`Json.tla`'s `ndJsonDeserialize`, and others — are normally paired with a compiled
Java class (`tlc2/overrides/*.class`, bundled in the same jar) that TLC loads as a
runtime override, giving the operator real behavior. Our harness only ever put the
extracted `.tla` files on `-DTLA-Library`, never the jar itself, so these operators
fall back to their bare TLA+ stub bodies — for `ndJsonDeserialize`, literally
`CHOOSE val : TRUE` (an intentionally-unconstrained placeholder, not a real
deserializer).

**Confirmed this is the correct, unavoidable tradeoff, not an oversight to fix:**
tried adding `CommunityModules-deps.jar` to the classpath directly (investigating
spec 78, below) — TLC immediately throws `NoClassDefFoundError:
tlc2/value/impl/KSubsetValue`. The jar was compiled against a newer `tla2tools.jar`
than our pinned release (`tools/TOOLS.md`'s own comment already said this:
"the CM fat jar bundles classes compiled against a newer tla2tools... and breaks TLC
if on the classpath" — confirmed by direct test, not just trusted). Our pinned
`tla2tools.jar` was itself chosen specifically because the *older* jar in
`tla_benchmark/` mis-parses TLAPS proof syntax — upgrading further to match the CM
jar risks reintroducing that or a different incompatibility, against the 156 specs
already closed. Not attempted.

**Spec 78 (EWD998ChanTrace) specifically:** confirmed the upstream trace file exists
(`tla-examples/specifications/ewd998/EWD998ChanTrace.ndjson`, 655 lines) and the
corpus's module is byte-identical to upstream. With the file vendored and a flat
(non-nested) path, dependency resolution and parsing succeed fully — the module
reaches real TLC execution — but `TraceN == JsonLog[1].N` needs `ndJsonDeserialize`
to actually parse the file, which needs the Java override this environment can't load.
Genuinely blocked by the classpath incompatibility above, not a corpus or cfg issue.

**Integrity check:** cross-referenced every corpus spec that `EXTENDS Json` or `CSV`
(109, 58, 75, 78, 81, 85, 77, 76, 80, 84) against the closed-spec list — **none of
them are currently closed**. All are already open/deferred for other reasons (TLCExt
missing, simulation-mode gaps, this trace-file gap). No retroactive concern about a
"clean pass" secretly resting on stub behavior.
