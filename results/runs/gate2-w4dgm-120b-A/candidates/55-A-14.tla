---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, echo, acked, pending

vars == <<parent, echo, acked, pending>>

Recurse(n) == IF parent[n] = NoNode THEN 0 ELSE 1 + Recurse(parent[n])

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ echo \in [Node -> BOOLEAN]
    /\ acked \in [Node -> BOOLEAN]
    /\ pending \subseteq (Node \X Node)

AncestorProperties ==
    /\ (FORALL n \in Node : (n # initiator) => (parent[n] # NoNode))
    /\ (FORALL n \in Node : n # initiator => (parent[parent[n]] # NoNode))
    /\ (Recurse(initiator) = 0)
    /\ (FORALL n \in Node : n # initiator => Recurse(n >= 1)

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ echo = [n \in Node |-> FALSE]
    /\ acked = [n \in Node |-> FALSE]
    /\ pending = {}

SendEcho ==
    /\ (\E s, t \in Node :
          /\ s # t
          /\ parent[t] = NoNode
          /\ <<s, t>> \notin pending
          /\ parent' = [parent EXCEPT ![t] = s]
          /\ pending' = pending \cup {<<s, t>>})
    /\ UNCHANGED <<echo, acked>>

EchoBack ==
    /\ (\E s, t \in Node :
          /\ <<s, t>> \in pending
          /\ s # initiator
          /\ pending' = pending \ {<<s, t>>}
          /\ echo' = [echo EXCEPT ![t] = TRUE]
          /\ parent' = [parent EXCEPT ![t] = IF s = initiator THEN NoNode ELSE s]
          /\ acked' = IF s = initiator THEN [acked EXCEPT ![t] = TRUE] ELSE acked)
    /\ UNCHANGED <<acked>>

FinalAck ==
    /\ (\E s, t \in Node :
          /\ <<s, t>> \in pending
          /\ s = initiator
          /\ pending' = pending \ {<<s, t>>}
          /\ echo' = [echo EXCEPT ![t] = TRUE]
          /\ acked' = [acked EXCEPT ![t] = TRUE]
          /\ parent' = [parent EXCEPT ![t] = NoNode])
    /\ UNCHANGED <<acked>>

Quiesce ==
    /\ (\A n \in Node : acked[n])
    /\ UNCHANGED vars

Raise ==
    /\ (\E n \in Node : ~echo[n] /\ parent[n] # NoNode /\ echo' = [echo EXCEPT ![n] = TRUE])
    /\ UNCHANGED <<parent, acked, pending>>

Next == SendEcho \/ EchoBack \/ FinalAck \/ Quiesce \/ Raise

Init == Init

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(SendEcho)
    /\ WF_vars(EchoBack)
    /\ WF_vars(FinalAck)
    /\ WF_vars(Raise)

TestSpec ==
    /\ Spec
    /\ \E e \in Node \X Node : pending = {e}

N1 == Node
I1 == initiator
R1 == R

====