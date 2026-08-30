---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

Sentinel == "sentinel"

Variable == "Variable"
Variable2 == "Variable2"
Variable3 == "Variable3"
Variable4 == "Variable4"
Variable5 == "Variable5"
Variable6 == "Variable6"
pc == "pc"

FreeVars == {Variable, Variable2, Variable3, Variable4, Variable5, Variable6, pc}

vars == <<Variable, Variable2, Variable3, Variable4, Variable5, Variable6, pc>>

Step == {"outerCheck", "lookup", "innerLoop", "updateBest", "follow", "postCompare", "increment", "done"}

TypeOK ==
  /\ Variable \in [1..Cardinality(CharacterSet)] -> CharacterSet
  /\ Variable2 \in Nat
  /\ Variable3 \in [1..2 * Cardinality(CharacterSet) -> Nat \cup {Sentinel}]
  /\ Variable4 \in Nat \cup {Sentinel}
  /\ Variable5 \in Nat
  /\ Variable6 \in 0..(Cardinality(CharacterSet) - 1)
  /\ pc \in Step

Init ==
  /\ \E s \in Seq(CharacterSet) : Variable = s
  /\ Variable2 = Len(Variable)
  /\ Variable3 = [i \in 1..(2 * Variable2) |-> Sentinel]
  /\ Variable4 = Sentinel
  /\ Variable5 = 1
  /\ Variable6 = 0
  /\ pc = "outerCheck"

OuterCheck ==
  /\ pc = "outerCheck"
  /\ pc' = IF Variable5 < 2 * Variable2 THEN "lookup" ELSE "done"
  /\ UNCHANGED <<Variable, Variable2, Variable3, Variable4, Variable5, Variable6>>

Lookup ==
  /\ pc = "lookup"
  /\ Variable3' = [Variable3 EXCEPT ![Variable5] = Variable3[Variable6]]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<Variable, Variable2, Variable4, Variable5, Variable6>>

InnerLoop ==
  /\ pc = "innerLoop"
  /\ Variable5 < Variable2 + Variable6
  /\ LET a == Variable[(Variable5 % Variable2) + 1] IN
     LET b == Variable[(Variable6 + Variable5) % Variable2 + 1] IN
       IF a # b /\ Variable4 # Sentinel THEN pc' = "innerLoop"
       ELSE pc' = "postCompare"
  /\ UNCHANGED <<Variable, Variable2, Variable3, Variable4, Variable5, Variable6>>

UpdateBest ==
  /\ pc = "updateBest"
  /\ LET a == Variable[(Variable5 % Variable2) + 1] IN
     LET b == Variable[(Variable6 + Variable5) % Variable2 + 1] IN
       IF a < b THEN Variable6' = Variable5 ELSE Variable6' = Variable6
  /\ pc' = "follow"
  /\ UNCHANGED <<Variable, Variable2, Variable3, Variable4, Variable5>>

Follow ==
  /\ pc = "follow"
  /\ Variable4 \in Nat
  /\ Variable3' = [Variable3 EXCEPT ![Variable5] = Variable4]
  /\ Variable4' = Sentinel
  /\ pc' = "postCompare"
  /\ UNCHANGED <<Variable, Variable2, Variable5, Variable6>>

PostCompare ==
  /\ pc = "postCompare"
  /\ LET a == Variable[(Variable5 % Variable2) + 1] IN
     LET b == Variable[(Variable6 + Variable5) % Variable2 + 1] IN
       /\ IF a # b /\ Variable4 = Sentinel /\ a < b THEN Variable6' = Variable5 ELSE Variable6' = Variable6
       /\ Variable3' = [Variable3 EXCEPT ![Variable5] = IF a # b THEN Sentinel ELSE (IF Variable4 = Sentinel THEN 1 ELSE Variable4 + 1)]
  /\ pc' = "increment"
  /\ UNCHANGED <<Variable, Variable2, Variable4, Variable5>>

Increment ==
  /\ pc = "increment"
  /\ Variable5' = Variable5 + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<Variable, Variable2, Variable3, Variable4, Variable6>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED FreeVars

Next ==
  \/ OuterCheck \/ Lookup \/ InnerLoop \/ UpdateBest \/ Follow \/ PostCompare \/ Increment \/ Done

Spec ==
  /\ Init
  /\ [][Next]_FreeVars
  /\ WF_vars(OuterCheck) /\ WF_vars(Lookup) /\ WF_vars(InnerLoop) /\ WF_vars(UpdateBest)
  /\ WF_vars(Follow) /\ WF_vars(PostCompare) /\ WF_vars(Increment)

TypeInvariant == TypeOK

Rotation(i) == SubSeq(Variable, i + 1, Len(Variable)) \o SubSeq(Variable, 1, i)

Correctness ==
  /\ pc = "done"
  /\ \A i \in 1..(Variable2 - 1) : Rotation(Variable6) <= Rotation(i)
  /\ (\A i \in 1..(Variable2 - 1) : Rotation(i) = Rotation(Variable6) => i >= Variable6)

Termination == (pc # "done") ~> (pc = "done")

====