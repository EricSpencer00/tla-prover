---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* Bounded sequence operator needed for a finite model
\* ----------------------------------------------------------------------
LimitedSeq(S) ==
  { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\* ----------------------------------------------------------------------
\* Concrete graph definition: each node has exactly two successors.
\* The .cfg will substitute this operator for the abstract Succ.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
  IF n \in Nodes THEN
    (* For illustration we connect each node to the next two nodes cyclically *)
    { ( (n + 1) % Cardinality(Nodes) ) , ( (n + 2) % Cardinality(Nodes) ) }
  ELSE {}

\* ----------------------------------------------------------------------
\* Reachability definition using bounded sequences
\* ----------------------------------------------------------------------
Reachable(n) ==
  \E s \in LimitedSeq(Nodes) :
    /\ Len(s) > 0
    /\ s[1] = Root
    /\ s[Len(s)] = n
    /\ \A i \in 1 .. Len(s)-1 :
         s[i+1] \in ConnectedToSomeButNotAll(s[i])

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Marked = {}
  /\ Frontier = {Root}
  /\ pc = "Running"

\* ----------------------------------------------------------------------
\* Transition relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "Running"
     /\ Frontier # {}
     /\ \E n \in Frontier:
          /\ Marked' = Marked \cup {n}
          /\ Frontier' = (Frontier \ {n})
                         \cup (ConnectedToSomeButNotAll[n] \ (Marked \cup Frontier))
          /\ pc' = "Running"
          /\ UNCHANGED << >>
  \/ /\ pc = "Running"
     /\ Frontier = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<Marked, Frontier>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Marked \subseteq Nodes
  /\ Frontier \subseteq Nodes
  /\ pc \in {"Running", "Done"}

\* ----------------------------------------------------------------------
\* Invariant 1: successor closure
\* ----------------------------------------------------------------------
Inv1 ==
  \A n \in Marked :
    \A s \in ConnectedToSomeButNotAll[n] :
      s \in Marked \/ s \in Frontier

\* ----------------------------------------------------------------------
\* Invariant 2: decomposition of reachable set
\* ----------------------------------------------------------------------
Inv2 ==
  \A n \in Nodes :
    (Reachable(n) => n \in Marked \/ n \in Frontier) /\
    (n \in Marked \/ n \in Frontier => Reachable(n))

\* ----------------------------------------------------------------------
\* Invariant 3: termination condition on frontier
\* ----------------------------------------------------------------------
Inv3 ==
  pc = "Done" => Frontier = {}

\* ----------------------------------------------------------------------
\* Partial correctness: when done, Marked equals the set of all reachable nodes
\* ----------------------------------------------------------------------
PartialCorrectness ==
  pc = "Done" => Marked = { n \in Nodes : Reachable(n) }

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====