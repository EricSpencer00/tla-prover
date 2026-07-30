---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ, Seq

ASSUME /\ Cardinality(Nodes) = 4
       /\ Root \in Nodes
       /\ Succ \in [Nodes -> SUBSET Nodes]
       /\ \A n \in Nodes : Cardinality(Succ[n]) = 2
       /\ Seq \subseteq (Nodes \X (0 .. Cardinality(Nodes)))
       /\ \A seq \in Seq : Len(seq) =< Cardinality(Nodes)

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

MarkedSet == { marked[i] : i \in DOMAIN marked }
FrontierSet == { frontier[i] : i \in DOMAIN frontier }

Init ==
  /\ marked = [i \in 1 .. 1 |-> Root]
  /\ frontier = [i \in 1 .. 1 |-> Root]
  /\ pc = "run"

\* Deterministic pick so the reachable state space stays finite; the
\* sequences in Succ are all bounded by the cardinality of Nodes.
Expand ==
  /\ pc = "run"
  /\ \E i \in DOMAIN frontier :
       /\ \E j \in Succ[frontier[i]] :
            /\ j \notin MarkedSet
            /\ marked' = [marked EXCEPT ![#marked + 1] = j]
            /\ frontier' = [frontier EXCEPT ![#frontier + 1] = j]
  /\ UNCHANGED pc

Complete ==
  /\ pc = "run"
  /\ frontier = [i \in DOMAIN frontier |-> Head(Seq)]
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Expand \/ Complete

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \in Seq
  /\ frontier \in Seq
  /\ pc \in {"run", "done"}

\* Reachability must be closed under immediate successors.
Inv1 ==
  \A n \in MarkedSet : \A m \in Succ[n] : m \in MarkedSet

\* The frontier nodes are always still reachable from the root.
Inv2 ==
  /\ frontier # {}
  /\ \E f \in frontier : f \in MarkedSet

\* Nodes reachable from the frontier are already covered.
Inv3 ==
  \A n \in Nodes :
    (\E f \in frontier : n \in Succ[f]) => n \in MarkedSet

PartialCorrectness ==
  pc = "done" => \A n \in Nodes : n \in MarkedSet

Termination ==
  <>(pc = "done")

====