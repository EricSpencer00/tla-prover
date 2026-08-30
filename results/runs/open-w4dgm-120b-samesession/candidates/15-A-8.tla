---------------------------- MODULE bcastByz ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, inbox, sent

vars == <<correct, faulty, pc, inbox, sent>>

Processes == 0..(N - 1)

TypeOK ==
    /\ correct \subseteq Processes
    /\ faulty \subseteq Processes
    /\ correct \cup faulty = Processes
    /\ correct \cap faulty = {}
    /\ pc \in [Processes -> {"init", "noinit", "sent", "accepted"}]
    /\ inbox \in [Processes -> SUBSET (Processes \X {"echo"})]
    /\ sent \subseteq (Processes \X {"echo"})

Init ==
    /\ correct = {p \in Processes : p < (N - F)}
    /\ faulty = Processes \ correct
    /\ pc = [p \in Processes |-> IF p < (N - F) THEN "init" ELSE "noinit"]
    /\ inbox = [p \in Processes |-> {}]
    /\ sent = {}

RecMsg(q) ==
    /\ inbox' = [inbox EXCEPT ![q] = inbox[q] \cup
                    {m \in sent : (m[1] \notin correct) \/ (m[2] = "echo")}]
    /\ UNCHANGED <<correct, faulty, pc, sent>>

InitAccept(p) ==
    /\ p \in correct
    /\ pc[p] = "init"
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ sent' = sent \cup {<<p, "echo">>}
    /\ UNCHANGED <<correct, faulty, inbox>>

EchoMid(p) ==
    /\ p \in correct
    /\ pc[p] \in {"init", "noinit"}
    /\ Cardinality(inbox[p]) >= (N - 2 * T)
    /\ Cardinality(inbox[p]) < (N - T)
    /\ sent' = sent \cup {<<p, "echo">>}
    /\ pc' = [pc EXCEPT ![p] = "sent"]
    /\ UNCHANGED <<correct, faulty, inbox>>

EchoAccept(p) ==
    /\ p \in correct
    /\ pc[p] \notin {"sent", "accepted"}
    /\ Cardinality(inbox[p]) >= (N - T)
    /\ sent' = sent \cup {<<p, "echo">>}
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ UNCHANGED <<correct, faulty, inbox>>

RelayAccept(p) ==
    /\ p \in correct
    /\ pc[p] = "sent"
    /\ Cardinality(inbox[p]) >= (N - T)
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ UNCHANGED <<correct, faulty, inbox, sent>>

Next ==
    \/ \E q \in Processes : RecMsg(q)
    \/ \E p \in Processes : InitAccept(p)
    \/ \E p \in Processes : EchoMid(p)
    \/ \E p \in Processes : EchoAccept(p)
    \/ \E p \in Processes : RelayAccept(p)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E q \in Processes : RecMsg(q))
        /\ WF_vars(\E p \in Processes : InitAccept(p))
        /\ WF_vars(\E p \in Processes : EchoMid(p))
        /\ WF_vars(\E p \in Processes : EchoAccept(p))
        /\ WF_vars(\E p \in Processes : RelayAccept(p))

CorrLtl == \A p \in correct : pc[p] = "init" ~> pc[p] = "accepted"

RelayLtl == (\E p \in correct : pc[p] = "accepted")
            ~> (\A q \in correct : pc[q] = "accepted")

UnforgLtl == (\A p \in correct : pc[p] = "noinit") ~> (\A q \in correct : pc[q] # "accepted")

FCConstraints ==
    /\ correct \cap faulty = {}
    /\ correct \cup faulty = Processes
    /\ N > 3 * T
    /\ T >= F

=============================================================================