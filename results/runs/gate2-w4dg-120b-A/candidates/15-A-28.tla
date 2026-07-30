---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A process is either correct or Byzantine. Correct processes follow the
\* single-round SRMV protocol; Byzantine processes may emit arbitrary ECHO
\* messages, so their messages are modeled as "all of them".
\* Control location: broadcast-received (B) or not (N). Action: dropped into
\* the send-and-act block so that weak fairness on it is what drives progress.
\* Unforgeability only needs the safety of the state, not the fairness.

Processes == 1..N
MsgKinds == {"ECHO"}
Messages == [snd : Processes, kind : MsgKinds]
Configs == {"B", "N"}

VARIABLES correct, faulty, pc, inbox, sent

vars == << correct, faulty, pc, inbox, sent >>

AllSent == Union({sent[p] : p \in correct})
AllObserved == Union({inbox[p] : p \in correct}) \cup { [snd |-> q, kind |-> "ECHO"] : q \in faulty }

TypeOK ==
    /\ correct \subseteq Processes
    /\ faulty \subseteq Processes
    /\ correct \cup faulty = Processes
    /\ correct \cap faulty = {}
    /\ pc \in [Processes -> Configs]
    /\ inbox \in [Processes -> SUBSET Messages]
    /\ sent \in [Processes -> SUBSET Messages]

\* The unforgeability invariant is only about state; the fairness it needs is
\* the one on the receive-and-act block, which is left off for the pure-safety check.
FCConstraints ==
    /\ Cardinality(correct) = N - F
    /\ Cardinality(faulty) = F
    /\ \A p \in correct : pc[p] \in Configs
    /\ \A p \in Processes : \A m \in inbox[p] : m.kind \in MsgKinds

Init ==
    /\ correct \subseteq Processes
    /\ Cardinality(correct) = N - F
    /\ faulty = Processes \ correct
    /\ pc \in [Processes -> Configs]
    /\ inbox \in [Processes -> SUBSET Messages]
    /\ sent \in [Processes -> SUBSET Messages]

InitBroadcast ==
    /\ \A p \in correct : pc[p] = "B"
    /\ \A p \in Processes : inbox[p] = {}
    /\ \A p \in Processes : sent[p] = {}

InitNone ==
    /\ \A p \in correct : pc[p] = "N"
    /\ \A p \in Processes : inbox[p] = {}
    /\ \A p \in Processes : sent[p] = {}

Receive(p) ==
    /\ pc[p] \in Configs
    /\ \E news \in SUBSET AllObserved :
         inbox' = [inbox EXCEPT ![p] = @ \cup news]
    /\ UNCHANGED << correct, faulty, pc, sent >>

SendEcho(p) ==
    /\ p \in correct
    /\ pc[p] = "B"
    /\ pc' = [pc EXCEPT ![p] = "N"]
    /\ sent' = [sent EXCEPT ![p] = { [snd |-> p, kind |-> "ECHO" ] }]
    /\ UNCHANGED << correct, faulty, inbox >>

\* Just enough echoes to send, but not enough to accept.
SendEchoIfHeard(p) ==
    /\ p \in correct
    /\ pc[p] \in Configs
    /\ Cardinality({ m \in inbox[p] : m.kind = "ECHO" }) >= N - 2 * T
    /\ Cardinality({ m \in inbox[p] : m.kind = "ECHO" }) < N - T
    /\ pc' = [pc EXCEPT ![p] = "N"]
    /\ sent' = [sent EXCEPT ![p] = { [snd |-> p, kind |-> "ECHO" ] }]
    /\ UNCHANGED << correct, faulty, inbox >>

AcceptWithEcho(p) ==
    /\ p \in correct
    /\ pc[p] \in Configs
    /\ Cardinality({ m \in inbox[p] : m.kind = "ECHO" }) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "N"]
    /\ sent' = [sent EXCEPT ![p] = { [snd |-> p, kind |-> "ECHO" ] }]
    /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \cup { [snd |-> p, kind |-> "ECHO" ] }]
    /\ UNCHANGED << correct, faulty >>

ReceiveAndAct(p) == Receive(p) \/ SendEcho(p) \/ SendEchoIfHeard(p) \/ AcceptWithEcho(p)

Next == \E p \in Processes : ReceiveAndAct(p)

Spec == Init /\ [][Next]_vars
        /\ (\A p \in Processes : WF_vars(ReceiveAndAct(p)))

CorrLtl ==
    (N - F) > 0 => <>(\A p \in correct : pc[p] = "N")
RelayLtl == (\E p \in correct : pc[p] = "N") ~> (\A p \in correct : pc[p] = "N")
UnforgLtl == (\A p \in correct : pc[p] # "B") ~> (\A p \in correct : pc[p] # "N")

====