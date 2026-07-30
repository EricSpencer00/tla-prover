---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* Dispatch a proof obligation to one of the backend theorem provers.  Each
\* prover has its own timeout; 0 means the prover is not to be invoked.
RouteToZenon(n) == n >= 0
RouteToIsabelle(n) == n >= 0
RouteToCVC3(n) == n >= 0
RouteToYices(n) == n >= 0
RouteToVeriT(n) == n >= 0
RouteToZ3(n) == n >= 0
RouteToSPASS(n) == n >= 0
RouteToLS4(n) == n >= 0

\* Temporal logic proof rules: these are the rules from Lamport's "The Temporal
\* Logic of Actions".  They are included only to reserve their names; the
\* proof system does not invoke them as actions.
InvHold(y) ==
  /\ y # "TriviallyTrue"
  /\ \A z \in ("Step_" \cup "Inv_") : z \notin y

WfHold(y) == y \in ("WfStep_" \cup "WF_")
SfHold(y) == y \in ("SfStep_" \cup "SF_")
StepSimHold(y) == y \in ("SimStep_" \cup "Sim_")

\* Fundamental set-theoretic facts, always true, serving as the module's
\* safety properties.
SetExtensionality ==
  \A A, B \in SUBSET Nat :
    (\A x \in Nat : x \in A <=> x \in B) => A = B

NotEveryValue ==
  \A V \in SUBSET Nat :
    \E x \in Nat : x \notin V

TypeOK ==
  /\ Zenon \in Nat
  /\ Isabelle \in Nat
  /\ CVC3 \in Nat
  /\ Yices \in Nat
  /\ veriT \in Nat
  /\ Z3 \in Nat
  /\ SPASS \in Nat
  /\ LS4 \in Nat

Spec == SpecA \cup SpecB
SpecA == \E n \in Nat : RouteToZenon(n) \/ RouteToIsabelle(n)
SpecB == \E n \in Nat : RouteToCVC3(n) \/ RouteToYices(n)
Init == TRUE
Next == TRUE
Invariants == SetExtensionality
Properties == NotEveryValue

====