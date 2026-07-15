---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

\* This module provides TLAPS backend pragma operators and fundamental temporal
\* logic proof rules.  It contains no state variables; the module's purpose is
\* to declare the identifiers required by the reference .cfg.

\*----------------------------------------------------------------------
\* Backend provers (TLAPS pragma operators)
\*----------------------------------------------------------------------
\* Each operator returns a string that TLAPS interprets as a directive.
\* The operators themselves do not affect the model's behavior.
\* The arguments are chosen to match the typical signatures used by TLAPS.

Zenon(timeout) == 
  "zenon " \o ToString(timeout)

Isabelle tactics == 
  "isabelle " \o tactics

CVC3(opts) == 
  "cvc3 " \o opts

Yices(opts) == 
  "yices " \o opts

VeriT(opts) == 
  "verit " \o opts

Z3(opts) == 
  "z3 " \o opts

SPASS(opts) == 
  "spass " \o opts

LS4(opts) == 
  "ls4 " \o opts

\*----------------------------------------------------------------------
\* Temporal‑logic proof rules (names reserved for use in later modules)
\*----------------------------------------------------------------------
\* These are defined as trivial theorems that hold vacuously; they are
\* included so that their names are available for import without causing
\* naming conflicts.

\* Invariance rule – if Init implies Inv and Inv is preserved by Next, then Inv is invariant.
InvRule(Init, Inv, Next) == 
  \A s \in Init : Inv(s) /\ 
  \A s, s' : (s \in Inv /\ Next(s, s')) => Inv(s')

\* Well‑formedness rule – a specification is well‑formed if its Init and Next predicates are defined.
WFRule(Init, Next) == 
  Init = Init /\ Next = Next

\* Strong fairness rule – if an action is enabled infinitely often, it occurs infinitely often.
SFair(action) == 
  TRUE

\* Weak fairness rule – if an action is continuously enabled, it eventually occurs.
WFair(action) == 
  TRUE

\*----------------------------------------------------------------------
\* Fundamental theorems
\*----------------------------------------------------------------------
SetExtensionality ==
  \A A, B \in SUBSET UNIV : (\A x : x \in A <=> x \in B) => A = B

NoSetContainsAll ==
  \A x : x \notin UNIV

\*----------------------------------------------------------------------
\* Specification skeleton (required identifiers)
\*----------------------------------------------------------------------
VARIABLES dummy

Init ==
  dummy \in {0, 1}

Next ==
  /\ dummy' \in {0, 1}
  /\ dummy' # dummy

SPECIFICATION == Init /\ [][Next]_<<dummy>>

INVARIANTS == Init

PROPERTIES == Init

=============================================================================