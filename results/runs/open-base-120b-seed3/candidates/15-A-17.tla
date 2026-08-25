---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N, T, F

\* Process identifiers
Proc == 1 .. N

\* Message type (only ECHO)
Message == [sender : Proc, type : {"ECHO"}]

\* State variables
VARIABLES correct, faulty, pc, recv, sent

\* Helper definitions
AllMsgs == sent \cup { [sender |-> b, type |-> "ECHO"] : b \in faulty }

EchoSenders(rec) == { m.sender : m \in rec /\ m.type = "ECHO" }

\* Initial state
Init ==
    /\ correct \subseteq Proc
    /\ Cardinality(correct) = N - F
    /\ faulty = Proc \ correct
    /\ \E initSet \in SUBSET correct :
          pc = [p \in Proc |-> IF p \in initSet THEN "InitRecv" ELSE "NoInit"]
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* One step for a correct process p that may receive new messages (new)
\* and possibly send an ECHO and/or accept.
Step(p, new) ==
    LET newRecv == recv[p] \cup new IN
    LET senders == EchoSenders(newRecv) IN
    LET mustSendEcho ==
        \/ pc[p] = "InitRecv"
        \/ (pc[p] = "NoInit" /\ Cardinality(senders) >= N - 2*T /\ Cardinality(senders) < N - T)
        \/ (pc[p] = "NoInit" /\ Cardinality(senders) >= N - T)
        \/ (pc[p] = "EchoSent" /\ Cardinality(senders) >= N - T)
    IN
    /\ p \in correct
    /\ new \subseteq AllMsgs
    /\ new \cap recv[p] = {}
    /\ recv' = [recv EXCEPT ![p] = newRecv]
    /\ sent' = IF mustSendEcho
               THEN sent \cup { [sender |-> p, type |-> "ECHO"] }
               ELSE sent
    /\ pc' =
        IF pc[p] = "InitRecv" THEN "Accepted"
        ELSE IF pc[p] = "NoInit" /\ Cardinality(senders) >= N - T THEN "Accepted"
        ELSE IF pc[p] = "NoInit" /\ Cardinality(senders) >= N - 2*T /\ Cardinality(senders) < N - T THEN "EchoSent"
        ELSE IF pc[p] = "EchoSent" /\ Cardinality(senders) >= N - T THEN "Accepted"
        ELSE pc[p]
    /\ UNCHANGED <<correct, faulty>>

\* Next relation: any correct process can take a step
Next ==
    \E p \in correct :
        \E new :
            Step(p, new)

\* Tuple of all variables for stuttering
vars == <<correct, faulty, pc, recv, sent>>

\* Specification with weak fairness on Next
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Type invariants
TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ pc \in [Proc -> {"InitRecv", "NoInit", "EchoSent", "Accepted"}]
    /\ sent \subseteq { [sender |-> p, type |-> "ECHO"] : p \in Proc }
    /\ recv \in [Proc -> SUBSET { [sender |-> p, type |-> "ECHO"] : p \in Proc }]

\* Fault‑tolerance constraints
FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0
    /\ Cardinality(correct) = N - F

\* Liveness properties
CorrLtl == ( \A p \in correct : pc[p] = "InitRecv" )
            => <> ( \A p \in correct : pc[p] = "Accepted" )

RelayLtl == ( \E p \in correct : pc[p] = "Accepted" )
            => <> ( \A p \in correct : pc[p] = "Accepted" )

\* Safety (unforgeability) property
UnforgLtl == [] ( ( \A p \in correct : pc[p] = "NoInit" )
                  => ( \A p \in correct : pc[p] # "Accepted" ) )

====