---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(***************************************************************************)
(*  TLAPS: Backend configuration and basic temporal‑logic proof rules.    *)
(*  This module provides placeholder definitions for the operators that   *)
(*  the TLA+ Proof System (TLAPS) expects to exist, so that a generated    *)
(*  .cfg file that refers to them will type‑check.                         *)
(*                                                                       *)
(*  No state variables, actions, or concrete behavior are modeled here;  *)
(*  the module only declares the names required by the configuration.    *)
(***************************************************************************)

\* ----------------------------------------------------------------------
\*  Configuration constants (place‑holders for prover names, timeouts, etc.)
\* ----------------------------------------------------------------------
CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* ----------------------------------------------------------------------
\*  Backend‑selection operators – they merely return the name of the
\*  prover that would be invoked.  The arguments are not used; they are
\*  present so that TLAPS can refer to them.
\* ----------------------------------------------------------------------
ZenonBackend(s)     == "Zenon"
IsabelleBackend(s)  == "Isabelle"
CVC3Backend(s)       == "CVC3"
YicesBackend(s)      == "Yices"
VeriTBackend(s)      == "veriT"
Z3Backend(s)         == "Z3"
SPASSBackend(s)      == "SPASS"
LS4Backend(s)        == "LS4"

\* ----------------------------------------------------------------------
\*  Time‑out placeholders – return a natural‑number timeout.
\* ----------------------------------------------------------------------
ZenonTimeout   == 10
IsabelleTimeout== 10
CVC3Timeout    == 10
YicesTimeout   == 10
VeriTTimeout   == 10
Z3Timeout      == 10
SPASSTimeout   == 10
LS4Timeout     == 10

\* ----------------------------------------------------------------------
\*  The SPECIFICATION operator is required by the .cfg.  As this module
\*  does not model any dynamics, SPECIFICATION simply yields TRUE.
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE

\* ----------------------------------------------------------------------
\*  INIT and NEXT are also required by many .cfg files.  We define a
\*  dummy state variable that never changes, allowing the model to be
\*  trivially initialized and to have a trivial stuttering NEXT.
\* ----------------------------------------------------------------------
VARIABLE dummy

InitDummy == /\ dummy \in {0}
NextDummy == /\ UNCHANGED dummy

INIT == InitDummy
NEXT == NextDummy

\* ----------------------------------------------------------------------
\*  INVARIANTS – the .cfg may list invariants to check.  We provide two
\*  fundamental theorems as invariants, expressed as constant formulas.
\* ----------------------------------------------------------------------
SetExtensionality == 
  \A A, B \in SUBSET Nat :
    (\A x \in Nat : x \in A <=> x \in B) => A = B

NoSetContainsAllValues == 
  \A A \in SUBSET Nat : \E x \in Nat : x \notin A

INVARIANTS == { SetExtensionality, NoSetContainsAllValues }

\* ----------------------------------------------------------------------
\*  PROPERTIES – placeholder for any additional temporal properties.
\*               Here we simply state that the dummy variable never
\*               changes, which is trivially true.
\* ----------------------------------------------------------------------
Stutter == [] (dummy' = dummy)
PROPERTIES == { Stutter }

\* ----------------------------------------------------------------------
\*  Temporal‑logic proof‑rule placeholders (names only, no semantics).
\* ----------------------------------------------------------------------
InvRule          == "InvRule"
WFRule           == "WFRule"
SFRule           == "SFRule"
StepSimRule      == "StepSimRule"
WellFormedRule   == "WellFormedRule"

=============================================================================