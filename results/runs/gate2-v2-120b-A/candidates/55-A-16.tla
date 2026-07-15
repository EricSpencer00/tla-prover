---- MODULE MCEcho ----
EXTENDS Naturals, TLC

\* ----------------------------------------------------------------------
\* Constants required by the reference configuration
\* ----------------------------------------------------------------------
CONSTANTS Node, initiator, R, NoNode

\* ----------------------------------------------------------------------
\* State variables inherited from the Echo specification
\* ----------------------------------------------------------------------
VARIABLES parent, children, acked, pending

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Children == [n \in Node |-> children[n]]

\* ----------------------------------------------------------------------
\* Initial predicate (inherits Echo's INIT, instantiated for the concrete graph)
\* ----------------------------------------------------------------------
Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ children = [n \in Node |-> {}]
    /\ acked = [n \in Node |-> FALSE]
    /\ pending = {initiator}
    /\ initiator \in Node

\* ----------------------------------------------------------------------
\* Next-state relation (inherits Echo's NEXT, unchanged)
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pending # {}
       /\ \E n \in pending :
          /\ pending' = pending \ {n}
          /\ IF parent[n] = NoNode THEN
                /\ parent' = [parent EXCEPT ![n] = initiator]
                /\ children' = [children EXCEPT ![initiator] = children[initiator] \cup {n}]
                /\ acked' = [acked EXCEPT ![n] = FALSE]
                /\ UNCHANGED <<>>
             ELSE
                /\ acked' = [acked EXCEPT ![n] = TRUE]
                /\ UNCHANGED <<parent, children, pending>>
    \/ /\ \E n \in Node :
          /\ acked[n]
          /\ \E m \in children[n] :
                /\ acked' = [acked EXCEPT ![n] = FALSE, ![m] = TRUE]
                /\ UNCHANGED <<parent, children, pending>>

\* ----------------------------------------------------------------------
\* Specification formula required by the .cfg
\* ----------------------------------------------------------------------
TestSpec == Init /\ [][Next]_<<parent, children, acked, pending>>

\* ----------------------------------------------------------------------
\* Safety invariant: type correctness (borrowed from Echo)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ children \in [Node -> SUBSET Node]
    /\ acked \in [Node -> BOOLEAN]
    /\ pending \in SUBSET Node
    /\ NoNode \notin Node
    /\ initiator \in Node
    /\ R \subseteq Node \X Node
    /\ \A <<i, j>> \in R : i # j
    /\ \A <<i, j>> \in R : <<j, i>> \in R

\* ----------------------------------------------------------------------
\* Safety invariant: ancestor properties (borrowed from Echo)
\* ----------------------------------------------------------------------
AncestorProperties ==
    /\ initiator \in {n \in Node : n # NoNode}
    /\ \A n \in Node :
         (n # initiator) => n \in REACHABLE(initiator, parent)
    /\ \A n \in Node : NoNode \notin REACHABLE(n, parent)

\* ----------------------------------------------------------------------
\* Helper definition for reachability via the parent relation
\* ----------------------------------------------------------------------
REACHABLE(start, par) ==
    { n \in Node :
        \E seq \in Seq(Node) :
          /\ Len(seq) > 0
          /\ seq[1] = start
          /\ seq[Len(seq)] = n
          /\ \A i \in 1..Len(seq)-1 : par[seq[i+1]] = seq[i] }

\* ----------------------------------------------------------------------
\* Theorem stating that the specification satisfies the invariants
\* ----------------------------------------------------------------------
THEOREM SpecImpliesSafety ==
    TestSpec => TypeOK /\ AncestorProperties

====