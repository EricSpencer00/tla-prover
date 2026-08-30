---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* N > 3T is required for the threshold bounds to be meaningful.
\* Correct processes follow the protocol; Byzantine processes may send
\* arbitrary ECHO messages that are ignored by the acceptance thresholds.
\* The "broadcasted" vs "not" start states model whether the singular
\* INIT message from the broadcaster was ever received.

VARIABLES correct, faulty, prog, rx, sent
vars == <<correct, faulty, prog, rx, sent>>

Stations == 0..(N - 1)
INITREC == "initRec"
INITNONE == "initNone"
EchoRecv == "echoRecv"
EchoNone == "echoNone"
MsgType == {"ECHO"}
StationSet == SUBSET Stations
InitMsgs == {<<s, INITREC>> : s \in Stations}
EchoMsgs == {<<s, "ECHO">> : s \in Stations}
AllMsgs == InitMsgs \cup EchoMsgs

TypeOK ==
    /\ correct \subseteq Stations
    /\ faulty \subseteq Stations
    /\ prog \in [Stations -> {INITREC, INITNONE, EchoRecv, EchoNone}]
    /\ rx \in [Stations -> SUBSET [sender: Stations, mtype: MsgType]]
    /\ sent \subseteq AllMsgs

\* A correct-or-faulty process may deliver any message that any correct
\* process has broadcast, plus any message a faulty process might forge.
Deliverable(m) == (m \in sent) \/ (\E s \in faulty : m \in {<<s, "ECHO">>})

Init ==
    /\ Cardinality(Stations) = N
    /\ correct \cup faulty = Stations
    /\ correct \cap faulty = {}
    /\ Cardinality(correct) = N - F
    /\ correct # {}
    /\ \E S \in [Stations -> {INITREC, INITNONE}] : prog = S
    /\ rx = [s \in Stations |-> {}]
    /\ sent = {}

\* The "no broadcast" variant starts with every correct process in INITNONE.
InitNoBcast ==
    /\ Init
    /\ \A s \in correct : prog[s] = INITNONE

EchoSenders(s) == {m.sender : m \in {x \in rx[s] : x.mtype = "ECHO"}}

RecvCorrect(s) ==
    /\ prog[s] # EchoRecv
    /\ \E M \in SUBSET {x \in sent : x.mtype = "ECHO"} :
         /\ M # {}
         /\ \A m \in M : m \in {<<p, "ECHO">> : p \in correct}
         /\ \A m \in M : m \notin rx[s]
         /\ rx' = [rx EXCEPT ![s] = @ \cup M]
    /\ UNCHANGED <<correct, faulty, prog, sent>>

ReceiveStep ==
    \/ \E s \in correct : RecvCorrect(s)
    \/ UNCHANGED <<correct, faulty, prog, sent>>

BroadcastInit(s) ==
    /\ prog[s] = INITREC
    /\ prog' = [prog EXCEPT ![s] = EchoRecv]
    /\ sent' = sent \cup {<<s, "ECHO">>}
    /\ UNCHANGED <<correct, faulty, rx>>

BroadcastEcho(s) ==
    /\ prog[s] = EchoNone
    /\ s \in correct
    /\ Cardinality(EchoSenders(s)) >= N - 2T
    /\ Cardinality(EchoSenders(s)) < N - T
    /\ prog' = [prog EXCEPT ![s] = EchoRecv]
    /\ sent' = sent \cup {<<s, "ECHO">>}
    /\ UNCHANGED <<correct, faulty, rx>>

AcceptLate(s) ==
    /\ prog[s] = EchoNone
    /\ Cardinality(EchoSenders(s)) >= N - T
    /\ prog' = [prog EXCEPT ![s] = EchoRecv]
    /\ sent' = sent \cup {<<s, "ECHO">>}
    /\ UNCHANGED <<correct, faulty, rx>>

AcceptLateStep ==
    \/ \E s \in correct : AcceptLate(s)
    \/ UNCHANGED <<correct, faulty, prog, rx, sent>>

AcceptAlreadySent(s) ==
    /\ prog[s] = EchoRecv
    /\ Cardinality(EchoSenders(s)) >= N - T
    /\ prog' = [prog EXCEPT ![s] = EchoRecv]
    /\ UNCHANGED <<correct, faulty, rx, sent>>

AcceptStep ==
    \/ \E s \in correct : AcceptAlreadySent(s)
    /\ UNCHANGED <<correct, faulty, prog, rx, sent>>

Next == ReceiveStep \/ BroadcastInitStep \/ BroadcastEchoStep \/ AcceptLateStep \/ AcceptStep

Spec == Init /\ [][Next]_vars
        /\ WF_vars(ReceiveStep)
        /\ WF_vars(BroadcastInitStep)
        /\ WF_vars(BroadcastEchoStep)
        /\ SF_vars(AcceptLateStep)
        /\ WF_vars(AcceptStep)

FCConstraints ==
    /\ correct \cap faulty = {}
    /\ correct \cup faulty = Stations

CorrLtl == <>(\A s \in correct : prog[s] = EchoRecv)
RelayLtl == (\E s \in correct : prog[s] = EchoRecv) ~> (\A s \in correct : prog[s] = EchoRecv)

\* If every correct process got the INIT broadcast, the network cannot
\* forever fail to deliver: every correct process eventually accepts.
UnforgLtl == (\A s \in correct : prog[s] = INITREC) ~> (\A s \in correct : prog[s] = EchoRecv)
====