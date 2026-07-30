---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Control locations: whether the process received the INIT message, has not
\* received it, has sent an ECHO, or has accepted a delivered value.
ControlLoc == {"broadcast", "nobroadcast", "echoed", "accepted"}

MessageKinds == {"echo"}

VARIABLES correctProcesses, faultyProcesses, loc, inbox, sentMsgs
vars == <<correctProcesses, faultyProcesses, loc, inbox, sentMsgs>>

TypeOK ==
    /\ correctProcesses \subseteq (1..N)
    /\ faultyProcesses \subseteq (1..N)
    /\ loc \in [1..N -> ControlLoc]
    /\ inbox \in [1..N -> SUBSET [(1..N) \X MessageKinds]]
    /\ sentMsgs \subseteq ((1..N) \X MessageKinds)

Init ==
    /\ correctProcesses = {1..(N - F)}
    /\ faultyProcesses = (1..N) \ correctProcesses
    /\ loc = [p \in 1..N |-> IF p <= (N - F) THEN "nobroadcast" ELSE "broadcast"]
    /\ inbox = [p \in 1..N |-> {}]
    /\ sentMsgs = {}

RecvCorrect(p) ==
    /\ loc[p] \notin {"echoed", "accepted"}
    /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \cup (sentMsgs \cup (faultyProcesses \X MessageKinds))]
    /\ UNCHANGED <<correctProcesses, faultyProcesses, loc, sentMsgs>>

\* A process that started with the INIT message accepts immediately and ECHOs.
ActOnInit(p) ==
    /\ loc[p] = "broadcast"
    /\ loc' = [loc EXCEPT ![p] = "accepted"]
    /\ sentMsgs' = sentMsgs \cup {<<p, "echo">>}
    /\ UNCHANGED <<correctProcesses, faultyProcesses, inbox>>

\* A correct process that has not yet sent ECHO receives enough ECHOs to send,
\* but not enough yet to accept; it acts on the received messages.
FirstStageEcho(p) ==
    /\ loc[p] \notin {"echoed", "accepted"}
    /\ loc[p] # "broadcast"
    /\ Cardinality({q \in 1..N : <<q, "echo">> \in inbox[p]}) >= (N - 2 * T)
    /\ loc[p] # "accepted"
    /\ loc[p] # "echoed"
    /\ loc' = [loc EXCEPT ![p] = "echoed"]
    /\ sentMsgs' = sentMsgs \cup {<<p, "echo">>}
    /\ UNCHANGED <<correctProcesses, faultyProcesses, inbox>>

\* A correct process that has not yet sent ECHO receives enough ECHOs to accept:
\* it sends ECHO and accepts in the same step.
SecondStageEcho(p) ==
    /\ loc[p] \notin {"echoed", "accepted"}
    /\ loc[p] # "broadcast"
    /\ Cardinality({q \in 1..N : <<q, "echo">> \in inbox[p]}) >= (N - T)
    /\ loc' = [loc EXCEPT ![p] = "accepted"]
    /\ sentMsgs' = sentMsgs \cup {<<p, "echo">>}
    /\ UNCHANGED <<correctProcesses, faultyProcesses, inbox>>

\* A correct process that already sent ECHO accepts once it accumulates enough.
LateAccept(p) ==
    /\ loc[p] \in {"echoed"}
    /\ Cardinality({q \in 1..N : <<q, "echo">> \in inbox[p]}) >= (N - T)
    /\ loc' = [loc EXCEPT ![p] = "accepted"]
    /\ UNCHANGED <<correctProcesses, faultyProcesses, inbox, sentMsgs>>

AllCorrectAccept == \A p \in correctProcesses : loc[p] = "accepted"

Next ==
    \/ \E p \in 1..N : RecvCorrect(p)
    \/ \E p \in 1..N : ActOnInit(p)
    \/ \E p \in 1..N : FirstStageEcho(p)
    \/ \E p \in 1..N : SecondStageEcho(p)
    \/ \E p \in 1..N : LateAccept(p)

\* Weak fairness on the combined receive-and-act steps of correct processes.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in correctProcesses : WF_vars(RecvCorrect(p))
    /\ \A p \in correctProcesses : WF_vars(ActOnInit(p))
    /\ \A p \in correctProcesses : WF_vars(FirstStageEcho(p))
    /\ \A p \in correctProcesses : WF_vars(SecondStageEcho(p))
    /\ \A p \in correctProcesses : WF_vars(LateAccept(p))

\* Unforgeable: if no correct process ever broadcasts, none accepts.
UnforgLtl == (\A p \in correctProcesses : loc[p] = "nobroadcast") ~> (\A p \in correctProcesses : loc[p] # "accepted")
CorrLtl == (\A p \in correctProcesses : loc[p] = "broadcast") ~> AllCorrectAccept
RelayLtl == (\E p \in correctProcesses : loc[p] = "accepted") ~> AllCorrectAccept

FCConstraints == Cardinality(correctProcesses) = (N - F)

====