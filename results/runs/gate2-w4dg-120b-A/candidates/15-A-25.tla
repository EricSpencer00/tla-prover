---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Correct processes broadcast INIT/ECHO; Byzantine may forge ECHO.
\* No designated broadcaster: ProcessVar encodes whether INIT arrived.
Processes == 1..N
MsgKinds == {"ECHO"}
MType == [src : Processes, kind : MsgKinds]

VARIABLES correct, faulty, loc, inbox, sent

vars == << correct, faulty, loc, inbox, sent >>

LocType == {"none", "hasINIT", "sentEcho", "accepted"}
LocInDomain == loc \in [Processes -> LocType]
InboxInDomain == inbox \in [Processes -> SUBSET MType]

TypeOK ==
    /\ correct \subseteq Processes
    /\ faulty \subseteq Processes
    /\ LocInDomain
    /\ InboxInDomain
    /\ sent \subseteq MType

\* Byzantine broadcast is modelled as every possible sender's message set.
AllPossibleMsgs == { [src |-> p, kind |-> k] : p \in Processes, k \in MsgKinds }

FCConstraints == /\ N > 3 * T
                 /\ T >= F
                 /\ F >= 0
                 /\ Cardinality(correct) = N - F
                 /\ correct \cap faulty = {}
                 /\ correct \cup faulty = Processes

\* No message traffic yet, and no process has accepted; correct/Byz partitioned.
Init ==
    /\ correct \cup faulty = Processes
    /\ correct \cap faulty = {}
    /\ loc = [p \in Processes |-> "none"]
    /\ inbox = [p \in Processes |-> {}]
    /\ sent = {}

\* No correct process ever receives the broadcaster's INIT message.
NoBroadcastInit ==
    /\ \A p \in Processes : loc[p] # "hasINIT"
    /\ loc' = loc
    /\ inbox' = inbox
    /\ sent' = sent
    /\ UNCHANGED << correct, faulty >>

\* A correct process may receive any new message set (correct+Byzantine).
ReceiveMsgs(p) ==
    /\ p \in correct
    /\ loc[p] # "accepted"
    /\ \E newMsgs \in SUBSET (sent \cup AllPossibleMsgs) :
         \A m \in newMsgs : m \notin inbox[p]
         inbox' = [inbox EXCEPT ![p] = inbox[p] \cup newMsgs]
    /\ UNCHANGED << correct, faulty, loc, sent >>

EchoSend(p) ==
    /\ p \in correct
    /\ loc[p] = "hasINIT"
    /\ loc' = [loc EXCEPT ![p] = "accepted"]
    /\ sent' = sent \cup { [src |-> p, kind |-> "ECHO"] }
    /\ UNCHANGED << correct, faulty, inbox >>

\* Enough ECHO for liveness, not yet for acceptance.
EchoEarly(p) ==
    /\ p \in correct
    /\ loc[p] = "none"
    /\ Cardinality({ m \in inbox[p] : m.kind = "ECHO" }) >= N - 2 * T
    /\ Cardinality({ m \in inbox[p] : m.kind = "ECHO" }) < N - T
    /\ loc' = [loc EXCEPT ![p] = "sentEcho"]
    /\ sent' = sent \cup { [src |-> p, kind |-> "ECHO"] }
    /\ UNCHANGED << correct, faulty, inbox >>

\* Enough ECHO to accept immediately; also sends ECHO as it does so.
EchoAndAccept(p) ==
    /\ p \in correct
    /\ loc[p] = "none"
    /\ Cardinality({ m \in inbox[p] : m.kind = "ECHO" }) >= N - T
    /\ loc' = [loc EXCEPT ![p] = "accepted"]
    /\ sent' = sent \cup { [src |-> p, kind |-> "ECHO"] }
    /\ UNCHANGED << correct, faulty, inbox >>

EchoDelayAccept(p) ==
    /\ p \in correct
    /\ loc[p] = "sentEcho"
    /\ Cardinality({ m \in inbox[p] : m.kind = "ECHO" }) >= N - T
    /\ loc' = [loc EXCEPT ![p] = "accepted"]
    /\ UNCHANGED << correct, faulty, inbox, sent >>

Next ==
    \E p \in Processes :
        \/ ReceiveMsgs(p) \/ EchoSend(p) \/ EchoEarly(p)
        \/ EchoAndAccept(p) \/ EchoDelayAccept(p) \/ NoBroadcastInit

Spec == Init /\ [][Next]_vars
        /\ \A p \in Processes : SF_vars(ReceiveMsgs(p))

AllCorrectAccepted == \A p \in correct : loc[p] = "accepted"

\* Unforgeability: with no INIT to start, no correct process accepts.
UnforgLtl == NoBroadcastInit ~> (\A p \in correct : loc[p] # "accepted")

CorrLtl == (\A p \in correct : loc[p] = "hasINIT") ~> AllCorrectAccepted
RelayLtl == (\E p \in correct : loc[p] = "accepted") ~> AllCorrectAccepted

====