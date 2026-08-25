---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

(***************************************************************************)
(*  Constants required by the configuration                               *)
(***************************************************************************)
CONSTANTS Nodes, Root, Succ   \* Succ will be overridden by ConnectedToSomeButNotAll

(***************************************************************************)
(*  State variables                                                        *)
(***************************************************************************)
VARIABLES Marked, Frontier, pc

(***************************************************************************)
(*  Bounded sequence definition                                            *)
(***************************************************************************)
MaxLen == Cardinality(Nodes)

LimitedSeq == { s \in Seq(Nodes) : Len(s) <= MaxLen }

(***************************************************************************)
(*  Successor function (finite version)                                    *)
(***************************************************************************)
ConnectedToSomeButNotAll(n) ==
  IF Cardinality(Nodes) < 3 THEN
    Nodes \ {n}
  ELSE
    LET first == CHOOSE m \in Nodes \ {n} : TRUE IN
    LET second == CHOOSE m \in (Nodes \ {n, first}) : TRUE IN
    {first, second}

(***************************************************************************)
(*  Initial state                                                          *)
(***************************************************************************)
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "run"

(***************************************************************************)
(*  Next-state relation                                                    *)
(***************************************************************************)
Next ==
  \/ /\ pc = "run"
     /\ \E n \in Frontier :
          /\ Frontier' = (Frontier \ {n}) \cup (ConnectedToSomeButNotAll(n) \ Marked)
          /\ Marked'   = Marked \cup {n}
          /\ pc'       = "run"
  \/ /\ pc = "run"
     /\ Frontier = {}
     /\ pc' = "done"
     /\ UNCHANGED <<Marked, Frontier>>

(***************************************************************************)
(*  Specification                                                          *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

(***************************************************************************)
(*  Invariants                                                             *)
(***************************************************************************)
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

Inv1 == \A n \in Marked : ConnectedToSomeButNotAll(n) \subseteq Marked

Inv2 == Frontier \subseteq Nodes \ Marked

Inv3 ==
  Marked = { n \in Nodes :
              \E s \in LimitedSeq :
                /\ Len(s) >= 1
                /\ s[1] = Root
                /\ s[Len(s)] = n
                /\ \A i \in 1..Len(s)-1 :
                     s[i+1] \in ConnectedToSomeButNotAll(s[i]) }

PartialCorrectness ==
  (pc = "done") => (Marked = Nodes)

(***************************************************************************)
(*  Liveness property                                                      *)
(***************************************************************************)
Termination == <> (pc = "done")

(***************************************************************************)
(*  The set of all invariants and properties for the model checker        *)
(***************************************************************************)
THEOREM TypeOKInvariant == Spec => []TypeOK
THEOREM Inv1Invariant == Spec => []Inv1
THEOREM Inv2Invariant == Spec => []Inv2
THEOREM Inv3Invariant == Spec => []Inv3
THEOREM PartialCorrectnessInvariant == Spec => []PartialCorrectness
THEOREM TerminationLiveness == Spec => Termination

=============================================================================