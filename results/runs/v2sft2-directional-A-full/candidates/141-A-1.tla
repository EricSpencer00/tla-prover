---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES Mk, F, pc

\* ------------------ Type Correctness invariant ------------------
TypeOK ==
  /\ Mk \subseteq Nodes
  /\ F \subseteq Nodes
  /\ pc \in {"Loop", "Terminated"}

\* ------------------ Initial state ------------------
Init ==
  /\ Mk = {}
  /\ F = {Root}
  /\ pc = "Loop"

\* ------------------ Main action ------------------
PickNode ==
  /\ pc = "Loop"
  /\ F # {}
  /\ \E n \in F :
       IF n \notin Mk THEN
           /\ Mk' = Mk \cup {n}
           /\ F' = F \cup Succ[n]
       ELSE
           /\ Mk' = Mk
           /\ F' = F \ {n}
       /\ pc' = pc

\* Termination action (stutter step) ----------
Terminate ==
  /\ pc = "Loop"
  /\ F = {}
  /\ pc' = "Terminated"
  /\ Mk' = Mk
  /\ F' = F

Spec ==
  Init /\ [][PickNode \/ Terminate]_<<Mk, F, pc>>

\* ------------------ Safety invariants (Partial correctness) ------------------
Inv1 ==
  \A n \in Mk :
      Succ[n] \subseteq Mk \cup F

Inv2 ==
  Mk \cup Reachable(F) = Reachable(Mk \cup F)

Inv3 ==
  Reachable(Root) = Mk \cup Reachable(F)

PartialCorrectness ==
  pc = "Terminated" => Inv3

\* ------------------ Liveness property (Termination) ------------------
Termination == WF_Act(PickNode)

====