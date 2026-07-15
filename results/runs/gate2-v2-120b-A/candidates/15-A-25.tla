---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ---------- Constants ----------
CONSTANT N
CONSTANT T
CONSTANT F

\* ---------- Derived Sets ----------
Proc == 1..N

\* ---------- Message Types ----------
MsgType == {"ECHO"}

Msg == [type : MsgType, sender : Proc]

\* ---------- State Variables ----------
VARIABLES
    correct,            \* set of correct processes
    faulty,             \* set of Byzantine processes
    pc,                 \* control location per process
    received,           \* set of messages received per process
    sent                \* set of messages sent by correct processes

\* ---------- Helper Definitions ----------
InitCorrectSet == { i \in Proc : i <= N - F }

ControlLoc == {"UNINIT", "ECHOED", "ACCEPTED"}

pcInit == [i \in Proc |-> "UNINIT"]
pcEchoed == [i \in Proc |-> "ECHOED"]
pcAccepted == [i \in Proc |-> "ACCEPTED"]

EmptySet == {}  \* shorthand

\* ---------- Initial State ----------
Init ==
    /\ correct = InitCorrectSet
    /\ faulty = Proc \ correct
    /\ pc = pcInit
    /\ received = [i \in Proc |-> EmptySet]
    /\ sent = EmptySet

\* ---------- Message Generation ----------
Echo(i) == [type |-> "ECHO", sender |-> i]

\* ---------- Actions ----------
\* 1. A correct process may receive any subset of messages that have been sent
\*    (by correct processes) or could be sent by Byzantine processes.
Receive(i) ==
    /\ i \in correct
    /\ LET newMsgs == 
            sent
            \cup { Echo(j) : j \in faulty }
          subset == SUBSET newMsgs
       IN
          /\ received' = [received EXCEPT ![i] = received[i] \cup subset]
    /\ UNCHANGED <<correct, faulty, pc, sent>>

\* 2. If a correct process already in ACCEPTED state, it stays there.
AcceptStutter(i) ==
    /\ i \in correct
    /\ pc[i] = "ACCEPTED"
    /\ UNCHANGED <<pc, received, sent, correct, faulty>>

\* 3. A correct process that has not yet sent ECHO may decide to send ECHO
\*    based on the number of distinct ECHO messages it has received.
SendEcho(i) ==
    /\ i \in correct
    /\ pc[i] = "UNINIT"
    /\ LET echoSenders == { m.sender : m \in received[i] /\ m.type = "ECHO" } UNION {i}
       IN
          /\ IF Cardinality(echoSenders) >= (N - T)
                THEN /\ pc' = [pc EXCEPT ![i] = "ACCEPTED"]
                     /\ sent' = sent \cup { Echo(i) }
                ELSE IF Cardinality(echoSenders) >= (N - 2 * T)
                        THEN /\ pc' = [pc EXCEPT ![i] = "ECHOED"]
                             /\ sent' = sent \cup { Echo(i) }
                        ELSE UNCHANGED <<pc, sent>>
    /\ UNCHANGED <<correct, faulty, received>>

\* 4. A correct process that has already sent ECHO may accept when it sees enough ECHOs.
AcceptAfterEcho(i) ==
    /\ i \in correct
    /\ pc[i] = "ECHOED"
    /\ LET echoSenders == { m.sender : m \in received[i] /\ m.type = "ECHO" } UNION {i}
       IN
          /\ Cardinality(echoSenders) >= (N - T)
          /\ pc' = [pc EXCEPT ![i] = "ACCEPTED"]
    /\ UNCHANGED <<correct, faulty, received, sent>>

\* 5. Stutter step for any correct process (allows fairness to operate).
Stutter(i) ==
    /\ i \in correct
    /\ UNCHANGED <<pc, received, sent, correct, faulty>>

\* 6. Non-deterministic choice of which correct process takes a step.
CorrectStep ==
    \/ \E i \in correct : Receive(i)
    \/ \E i \in correct : SendEcho(i)
    \/ \E i \in correct : AcceptAfterEcho(i)
    \/ \E i \in correct : AcceptStutter(i)
    \/ \E i \in correct : Stutter(i)

\* ---------- Next Relation ----------
Next == CorrectStep

\* ---------- Specification ----------
Spec == Init /\ [][Next]_<<pc, received, sent, correct, faulty>>

\* ---------- Type Safety Invariant ----------
TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ pc \in [Proc -> ControlLoc]
    /\ received \in [Proc -> SUBSET Msg]
    /\ sent \subseteq Msg
    /\ \A i \in Proc : \A m \in received[i] : m.type \in MsgType /\ m.sender \in Proc

\* ---------- Faulty-Correct Constraints ----------
FCConstraints ==
    /\ Cardinality(correct) = N - F
    /\ Cardinality(faulty) = F
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ---------- Safety Property: Unforgeability ----------
\* If no correct process ever receives an INIT (i.e., all start UNINIT), then
\* no correct process ever reaches ACCEPTED.
UnforgLtl ==
    ( \A i \in correct : pc[i] = "UNINIT" ) => ( \A i \in correct : pc[i] # "ACCEPTED" )

\* ---------- Liveness Property: Correctness ----------
CorrLtl ==
    ( \A i \in correct : pc[i] = "ACCEPTED" ) => <> ( \A i \in correct : pc[i] = "ACCEPTED" )

\* ---------- Liveness Property: Relay ----------
RelayLtl ==
    ( \E i \in correct : pc[i] = "ACCEPTED" ) => <> ( \A i \in correct : pc[i] = "ACCEPTED" )

=============================================================================