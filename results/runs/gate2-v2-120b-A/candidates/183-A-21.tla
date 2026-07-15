---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* Helper definitions                                                       *)
(***************************************************************************)

VARIABLES x, y

(***************************************************************************)
(* Backend pragma operators (placeholders)                                  *)
(***************************************************************************)

\* Each backend operator pretends to send the current proof obligation
\* to a corresponding prover with a given timeout.
\* The operators return TRUE, meaning the obligation is assumed provable.
\* The actual proof system replaces these definitions with the appropriate
\* calls during the proof compilation step.

Zenon(t) == TRUE
Isabelle(t) == TRUE
CVC3(t) == TRUE
Yices(t) == TRUE
veriT(t) == TRUE
Z3(t) == TRUE
SPASS(t) == TRUE
LS4(t) == TRUE

(***************************************************************************)
(* Temporal logic proof rule placeholders                                   *)
(***************************************************************************)

\* Invariance rule placeholder
InvRule(P) == TRUE

\* Well‑formedness rule placeholder
WFRule(P) == TRUE

\* Strong fairness rule placeholder
StrongFair(P) == TRUE

\* Weak fairness rule placeholder
WeakFair(P) == TRUE

\* Step simulation rule placeholder
StepSim(P) == TRUE

(***************************************************************************)
(* Core specifications and operators                                        *)
(***************************************************************************)

\* No state variables are required by the description, but we declare a
\* dummy variable to give the model a state.  Its value is irrelevant.
VARIABLE dummy

\* Initial predicate
Init == dummy = 0

\* Stuttering next action (the only action, does nothing)
Next == dummy' = dummy

\* The overall specification: infinite stuttering behavior
SPECIFICATION == Init /\ [][Next]_<<dummy>>

\* Safety invariant: set extensionality (trivial instance)
Extensionality ==
  \A A, B \subseteq {0,1} :
    (\A z : (z \in A) <=> (z \in B)) => A = B

\* Safety invariant: no set contains every possible value
NoUniversalSet ==
  \A S \subseteq {0,1} : S # {0,1}

INVARIANTS == Extensionality /\ NoUniversalSet

\* No liveness property is required
PROPERTIES == TRUE

(***************************************************************************)
(* Theorem statements (optional, for readability)                           *)
(***************************************************************************)

THEOREM SetExtensionality == Extensionality
THEOREM NoSetIsUniversal == NoUniversalSet

====