---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

\* Reachable: the adjacency operator; the .cfg substitutes a bounded version in.
Reachable(n) == Succ[n]

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE
           Rest == ReachFrom(S \ {x})
       IN {x} \cup ReachFrom(Reachable(x)) \cup Rest

ConnectedToSomeButNotAll == ReachFrom(Nodes)

NextFrontier(f, n) ==
  IF frontier = {n} THEN {}
  ELSE IF n \in f THEN frontier \ {n}
  ELSE f \cup {n}

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}
  /\ Root \in Nodes

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* The loop is nondeterministic both in action selection and in which frontier
\* node n it acts on (this is what lets the frontier and marked sets overlap).
Step(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ \/ /\ n \notin marked
        /\ marked' = marked \cup {n}
        /\ frontier' = NextFrontier(frontier, n)
        /\ UNCHANGED pc
     \/ /\ n \in marked
        /\ frontier' = frontier \ {n}
        /\ UNCHANGED <<marked, pc>>
  /\ UNCHANGED <<marked, frontier>>

Termination == /\ pc = "running" /\ frontier = {} /\ pc' = "done" /\ UNCHANGED <<marked, frontier>>
Next == (\E n \in Nodes: Step(n)) \/ Termination

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Bounded frontier may still carry a marked node; the successor of a marked node
\* is never lost -- it is either already marked or still in the frontier.
Inv1 ==
  /\ \A n \in marked : Reachable(n) \subseteq marked \cup frontier
  /\ ReachFrom(marked \cup frontier) = ReachFrom(Nodes)

Inv2 == ReachFrom(Nodes) = marked \cup ReachFrom(frontier)

Inv3 == ReachFrom(Nodes) \subseteq marked \cup frontier

PartialCorrectness == pc = "done" => marked = ReachFrom(Nodes)

\* If Reachable is finite, the algorithm cannot be stuck with a non-empty
\* frontier forever (each cycle shrinks frontier or grows the finite marked).
Termination == (Reachable \in FINITE) ~> (frontier = {})

LimitedSeq == Seq

====