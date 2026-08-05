---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, sent, collected, phase

vars == <<parent, sent, collected, phase>>

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ sent \in [Node -> BOOLEAN]
    /\ collected \in [Node -> SUBSET Node]
    /\ phase \in [Node -> {"idle", "sent", "collected"}]

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ sent = [n \in Node |-> FALSE]
    /\ collected = [n \in Node |-> {}]
    /\ phase = [n \in Node |-> IF n = initiator THEN "sent" ELSE "idle"]

SendEcho ==
    /\ phase[initiator] = "sent"
    /\ \E n \in Node, m \in Node :
        /\ n # m
        /\ R[n][m]
        /\ phase[n] = "idle"
        /\ phase[m] = "sent"
        /\ parent[n] = NoNode
        /\ parent' = [parent EXCEPT ![n] = m]
        /\ sent' = [sent EXCEPT ![n] = TRUE]
        /\ phase' = [phase EXCEPT ![n] = "sent"]
    /\ UNCHANGED collected

CollectAtLeaf ==
    /\ \E n \in Node :
        /\ phase[n] = "sent"
        /\ sent[n] = TRUE
        /\ sent' = [sent EXCEPT ![n] = FALSE]
        /\ phase' = [phase EXCEPT ![n] = "collected"]
        /\ collected' = [collected EXCEPT ![n] = {n}]
    /\ UNCHANGED parent

PropagateCollect ==
    /\ \E m \in Node :
        /\ phase[m] = "sent"
        /\ \E n \in Node :
            /\ parent[n] = m
            /\ n # m
            /\ phase[n] = "collected"
            /\ collected' = [collected EXCEPT ![m] = collected[m] \cup collected[n]]
            /\ phase' = [phase EXCEPT ![n] = "idle"]
    /\ UNCHANGED <<parent, sent>>

Done == \A n \in Node : phase[n] = "idle"

Next == SendEcho \/ CollectAtLeaf \/ PropagateCollect \/ (Done /\ UNCHANGED vars)

PrintGraph ==
    LET PrintRel ==
        BEGIN
            Print("R = {");
            \E n \in Node :
                \E m \in Node :
                    IF n # m /\ R[n][m] THEN Print("<<", n, ", ", m, ">>")
                    ELSE Print(""),
                    Print("}");
        END
    IN PrintRel

Spec == Init /\ [][Next]_vars
TestSpec == Spec /\ PrintGraph

AncestorProperties ==
    /\ \A n \in Node : (n # initiator /\ parent[n] # NoNode) => phase[n] = "collected"
    /\ \A n \in Node : (n # initiator /\ parent[n] # NoNode) => initiator \in collected[n]
    /\ \A n \in Node : parent[n] # NoNode => parent[n] \notin collected[n]

====