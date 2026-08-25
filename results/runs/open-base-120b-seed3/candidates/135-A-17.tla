---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

\*----------------------------------------------------------------------
\* Constants
\*----------------------------------------------------------------------

CONSTANTS Nodes, Root, Succ

\* Concrete values for the configuration (4 nodes, each with 2 successors)
Nodes == {"n1", "n2", "n3", "n4"}
Root  == "n1"

\* The bounded successor relation (used via the substitution ConnectedToSomeButNotAll)
ConnectedToSomeButNotAll ==
  [ "n1" |-> {"n2", "n3"},
    "n2" |-> {"n3", "n4"},
    "n3" |-> {"n1", "n4"},
    "n4" |-> {"n1", "n2"} ]

\* Provide an alias so that the constant Succ can be interpreted as the successor
\* function (the .cfg may replace Succ with ConnectedToSomeButNotAll)
Succ == ConnectedToSomeButNotAll

\*----------------------------------------------------------------------
\* Finite version of Seq (limits length to number of nodes)
\*----------------------------------------------------------------------

LimitedSeq(S) == { s \in Seq(S) : Len(s) <= Cardinality(Nodes) }

\*----------------------------------------------------------------------
\* State variables
\*----------------------------------------------------------------------

VARIABLES marked, frontier, pc

\*----------------------------------------------------------------------
\* Helper definitions
\*----------------------------------------------------------------------

\* A path from Root to n using the bounded successor relation
PathTo(n) ==
  \E p \in LimitedSeq(Nodes) :
    /\ Len(p) >= 1
    /\ p[1] = Root
    /\ p[Len(p)] = n
    /\ \A i \in 1..Len(p)-1 :
         p[i+1] \in ConnectedToSomeButNotAll[p[i]]

ReachableFromRoot(n) == PathTo(n)

\*----------------------------------------------------------------------
\* Initial predicate
\*----------------------------------------------------------------------

Init ==
  /\ marked   = {Root}
  /\ frontier = ConnectedToSomeButNotAll[Root]
  /\ pc       = "run"

\*----------------------------------------------------------------------
\* Next-state relation
\*----------------------------------------------------------------------

Next ==
  \/ /\ pc = "run"
     /\ frontier # {}
     /\ \E n \in frontier :
          /\ marked'   = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup (ConnectedToSomeButNotAll[n] \ marked)
          /\ UNCHANGED pc
  \/ /\ pc = "run"
     /\ frontier = {}
     /\ pc'      = "done"
     /\ UNCHANGED <<marked, frontier>>

\*----------------------------------------------------------------------
\* Specification
\*----------------------------------------------------------------------

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\*----------------------------------------------------------------------
\* Invariants
\*----------------------------------------------------------------------

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

Inv1 == marked = { n \in Nodes : ReachableFromRoot(n) }

Inv2 == frontier =
        { n \in Nodes :
            /\ ReachableFromRoot(n)
            /\ n \notin marked }

Inv3 == /\ frontier = {} => pc = "done"

PartialCorrectness == 
  /\ pc = "done"
  => marked = { n \in Nodes : ReachableFromRoot(n) }

\*----------------------------------------------------------------------
\* Properties
\*----------------------------------------------------------------------

Termination == <> (pc = "done")

\*----------------------------------------------------------------------
\* The set of invariants and properties required by the .cfg file
\*----------------------------------------------------------------------

\* (These names are exported automatically; the .cfg will refer to them)

\* End of module
====