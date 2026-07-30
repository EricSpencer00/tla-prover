---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

ASSUME Root \in Nodes

VARIABLES done, frontier, pc
vars == <<done, frontier, pc>>

RECURSIVE ReachableFrom(_)
ReachableFrom(S) ==
  IF S = {} THEN {}
  ELSE LET n == CHOOSE x \in S : TRUE IN Succ[n] \cup ReachableFrom(S \ {n})

TypeOK ==
  /\ done \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "idle"}

Init ==
  /\ done = {}
  /\ frontier = {Root}
  /\ pc = "running"

Step ==
  /\ frontier # {}
  /\ pc = "running"
  /\ \E n \in frontier :
       \/ /\ n \notin done
          /\ done' = done \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in done
          /\ frontier' = frontier \ {n}
          /\ done' = done
  /\ pc' = "running"

Terminate ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "idle"
  /\ UNCHANGED <<done, frontier>>

Next == Step \/ Terminate

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Step)

Inv1 ==
  \A n \in done : Succ[n] \subseteq done \cup frontier

Inv2 ==
  (done \cup frontier) \cup ReachableFrom(frontier) =
    (done \cup frontier) \cup ReachableFrom(done \cup frontier)

Inv3 ==
  ReachableFrom({Root}) = done \cup ReachableFrom(frontier)

PartialCorrectness ==
  \A n \in Nodes : (pc = "idle") => (n \in done) <=> (ReachableFrom({Root}) \ni n)

Termination ==
  Cardinality(ReachableFrom({Root})) \in Nat => (pc = "idle")
====