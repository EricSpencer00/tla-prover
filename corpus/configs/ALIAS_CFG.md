# ALIAS cfg keyword not supported by our pinned tla2tools.jar

Several specs' original `.cfg` files use TLC's `ALIAS` directive (a newer feature:
`ALIAS <op>` names an operator that reformats how states are printed in error traces
— purely cosmetic, doesn't change what's checked; every case found here has its own
`Alias == [ ... \* Pretty printing of error-trace states ... ]` comment confirming
this). Confirmed our pinned `tla2tools.jar` (`tools/TOOLS.md`) doesn't support it at
all: `java -cp tools/tla2tools.jar tlc2.TLC -help` doesn't list `ALIAS`, and cfgs that
use it fail with either `"The property/constraint ALIAS ... is not defined"` or a
harder `ConfigFileException: expecting a keyword, but did not find it` depending on
exactly where in the cfg it appears.

Fix: override cfg with the `ALIAS` stanza removed (both the two-line form,
`ALIAS\n    Alias`, and the one-line form, `ALIAS Alias` — the first attempt at this
missed the one-line form for spec 82, worth remembering if more turn up). Confirmed
directly that TLC then parses and explores real states.

## Resolved

- **59 (TokenRing)** — closed, clean pass.
- **82 (EWD998PCal)** — closed, clean pass (needed the one-line-form fix).
- **60 (EWD687a_anim), 64 (EWD840_anim), 100 (Huang)** — `ConfigFileException`/`ALIAS
  not defined` resolved (now parse and explore real states), but each times out —
  large state space, same disposition as the other confirmed timeouts.

## Other `ALIAS`-using specs, not reached by this fix

**18, 76** also use `ALIAS` but are blocked earlier in the pipeline (SANY-level
missing-module issues per `corpus/configs/SANY_FIXES.md`/`DEFERRED.json`) — stripping
`ALIAS` wouldn't matter until those are resolved first.
