---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES Marked, Frontier, pc

\* --- State predicates ------------------------------------------------

Init ==
    /\ Marked = {Root}
    /\ Frontier = {Root}
    /\ pc = "Init"

\* The algorithm proceeds by removing a node from Frontier,
   adding its successors, and stopping when Frontier is empty.

Next ==
    \/ /\ Frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<Marked, Frontier>>
    \/ \E n \in Frontier:
          LET newSucc == Succ[n] \ Marked IN
          /\ Marked'   = Marked \cup newSucc
          /\ Frontier' = (Frontier \ {n}) \cup newSucc
          /\ pc'       = "Step"
          /\ UNCHANGED Seq

Spec == Init /\ [][Next]_<<Marked, Frontier, pc>>

\* --- Helper definitions ----------------------------------------------

NodeSeq == Seq

\* --- Invariants -------------------------------------------------------

\* Type correctness: Marked and Frontier are subsets of Nodes,
   pc is one of the allowed control states, and NodeSeq is a finite
   sequence of nodes.
TypeOK ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"Init", "Step", "Done"}
    /\ NodeSeq \in Seq(Node)

\* Inv1: Every node in Marked is reachable from Root via a finite
   sequence of successors (uses the bounded sequence NodeSeq).
Inv1 ==
    \A n \in Marked :
        \E s \in NodeSeq :
            /\ Len(s) > 0
            /\ s[1] = Root
            /\ s[Len(s)] = n
            /\ \A i \in 1..Len(s)-1 : s[i+1] \in Succ[s[i]]

\* Inv2: The frontier consists exactly of those marked nodes that have
   at least one successor not yet marked.
Inv2 ==
    Frontier =
        { n \in Marked :
            \E m \in Succ[n] : m \notin Marked }

\* Inv3: The set of reachable nodes equals the set of marked nodes.
Inv3 ==
    Marked = Reachable

\* Reachable is defined as the least fixed point of the successor
   relation starting from Root, constrained to Nodes.
Reachable ==
    LET R == {Root}
    IN  UNION { S : S \in SUBSET Nodes /\ R \subseteq S /\ 
                \A n \in S : Succ[n] \subseteq S }
       \* The above characterises the smallest set containing Root and
       \* closed under Succ; for a finite graph this equals the usual
       \* reachable set.

PartialCorrectness ==
    \/ pc = "Done" => Marked = Reachable
    \/ pc # "Done"

Termination == <> (pc = "Done")

\* --- Specification components -----------------------------------------

TerminationInv == Termination

\* The identifiers required by the .cfg file
Spec          == Spec
Init          == Init
Next          == Next
TypeOK        == TypeOK
Inv1          == Inv1
Inv2          == Inv2
Inv3          == Inv3
PartialCorrectness == PartialCorrectness
Termination   == Termination

====