# Spec 72 (EWD998_anim) — partial progress, left open

**Corpus-file-format finding:** `data/tla_files/72.tla` is not a bare module — upstream
ships it with an embedded `---- CONFIG EWD998_anim ----` cfg block *before* the
`---- MODULE ----` block (a valid Toolbox convention TLC's `-config file.tla` flag
can parse directly from the combined file, but our harness expects exactly one module
per `.tla` file and the cfg supplied separately). Extracted the module portion to
`corpus/configs/patches/72.tla` and reproduced the embedded cfg (minus the unsupported
`ALIAS` stanza, `corpus/configs/ALIAS_CFG.md`) as `corpus/configs/overrides/72.cfg`.

This unblocked SANY (now passes) and got TLC into real `Init` computation (was a hard
`"constant parameter Node is not assigned"` error before) — but `Init` computation now
fails: `"Error: current state is not a legal state"`. `AnimSpec` (the cfg's
`SPECIFICATION`) manually constructs an initial state via a mix of direct assignment
and `Init!5` (the 5th disjunct of the underlying `EWD998Chan`'s `Init`, referenced
through the module's `EXTENDS EWD998ChanID` chain) — the constructed state doesn't
satisfy the base spec's own type/state constraints as assembled here.

Not root-caused further: this is fundamentally an SVG-animation demo spec (its own
header comments describe generating and viewing animation frames with Gnome's Eye of
Gnome, `IOExec`-shells out to `bash`+produces `.svg` files) — its real purpose has
nothing to do with correctness verification, and understanding exactly which of
`EWD998Chan`'s internal state fields `AnimSpec`'s hand-built init is missing would need
a level of protocol-internals digging disproportionate to what this spec is actually
for. Left open. If picked up again: compare `AnimSpec`'s manual field list against
`EWD998Chan`'s real `Init` definition field-by-field.
