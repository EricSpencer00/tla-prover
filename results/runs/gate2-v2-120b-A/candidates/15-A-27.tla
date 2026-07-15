---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N, T, F

\*--------------------------------------------------------------------
\* Types
\*--------------------------------------------------------------------
PCVals == {"NoInit", "InitReceived", "EchoSent", "Accepted"}

Message == [type : {"ECHO"}, sender : 1..N]

\*--------------------------------------------------------------------
\* Variables
\*--------------------------------------------------------------------
VARIABLES
    correct,          \* Set of correct process ids
    faulty,           \* Set of faulty process ids
    pc,               \* [proc -> PCVals] program counter
    received,         \* [proc -> SUBSET Message] messages received by each proc
    sent_echoes       \* SUBSET Message sent by correct processes

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
AllProcesses == 1..N

CorrectSendersSet(s) == { m.sender : m \in s }

ProcessSendsEcho(p) == [type |-> "ECHO", sender |-> p]

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
    /\ correct \subseteq AllProcesses
    /\ faulty = AllProcesses \ correct
    /\ Cardinality(correct) = N - F
    /\ pc = [p \in AllProcesses |-> IF p \in correct THEN "NoInit" ELSE "InitReceived"]
    /\ received = [p \in AllProcesses |-> {}]
    /\ sent_echoes = {}

\*--------------------------------------------------------------------
\* Actions
\*--------------------------------------------------------------------
\* (1) Receive any subset of messages that have been sent (including Byzantine)
Receive(p) ==
    /\ p \in correct
    /\ pc[p] \in {"NoInit", "InitReceived", "EchoSent", "Accepted"}
    /\ \E new \subseteq (sent_echoes \cup { ProcessSendsEcho(b) : b \in faulty }) :
        /\ received' = [received EXCEPT ![p] = received[p] \cup new]
        /\ UNCHANGED <<correct, faulty, pc, sent_echoes>>

\* (2) If process has received INIT (i.e., starts in InitReceived) and hasn't yet sent echo, it accepts and sends echo
AcceptAndEcho(p) ==
    /\ p \in correct
    /\ pc[p] = "InitReceived"
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent_echoes' = sent_echoes \cup { ProcessSendsEcho(p) }
    /\ UNCHANGED <<correct, faulty, received>>

\* (3) Send ECHO without accept when received >= N-2T distinct ECHO messages, but fewer than N-T
SendEchoNoAccept(p) ==
    /\ p \in correct
    /\ pc[p] = "NoInit"
    /\ LET distinctSenders == { m.sender : m \in received[p] } IN
        /\ Cardinality(distinctSenders) >= N - 2*T
        /\ Cardinality(distinctSenders) < N - T
    /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
    /\ sent_echoes' = sent_echoes \cup { ProcessSendsEcho(p) }
    /\ UNCHANGED <<correct, faulty, received>>

\* (4) Send ECHO and accept when received >= N-T distinct ECHO messages
SendEchoAndAccept(p) ==
    /\ p \in correct
    /\ pc[p] = "NoInit"
    /\ Cardinality({ m.sender : m \in received[p] }) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent_echoes' = sent_echoes \cup { ProcessSendsEcho(p) }
    /\ UNCHANGED <<correct, faulty, received>>

\* (5) Accept after already having sent ECHO and now receiving >= N-T distinct ECHO messages
AcceptAfterEcho(p) ==
    /\ p \in correct
    /\ pc[p] = "EchoSent"
    /\ Cardinality({ m.sender : m \in received[p] }) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<correct, faulty, received, sent_echoes>>

\* Combined step for a correct process
CorrectStep ==
    \E p \in correct :
        \/ Receive(p)
        \/ AcceptAndEcho(p)
        \/ SendEchoNoAccept(p)
        \/ SendEchoAndAccept(p)
        \/ AcceptAfterEcho(p)

\*--------------------------------------------------------------------
\* Next-state relation
\*--------------------------------------------------------------------
Next ==
    \/ CorrectStep
    \/ UNCHANGED <<correct, faulty, pc, received, sent_echoes>>

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<correct, faulty, pc, received, sent_echoes>>

\*--------------------------------------------------------------------
\* Invariants
\*--------------------------------------------------------------------
TypeOK ==
    /\ correct \subseteq AllProcesses
    /\ faulty = AllProcesses \ correct
    /\ Cardinality(correct) = N - F
    /\ pc \in [AllProcesses -> PCVals]
    /\ received \in [AllProcesses -> SUBSET Message]
    /\ sent_echoes \subseteq { ProcessSendsEcho(p) : p \in correct }

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\*--------------------------------------------------------------------
\* Safety property (Unforgeability) as invariant
\*--------------------------------------------------------------------
Unforgeability ==
    /\ \A p \in correct : pc[p] # "Accepted"
    \/ \E p \in correct : pc[p] = "InitReceived"

\*--------------------------------------------------------------------
\* Liveness properties (expressed as temporal formulas)
\*--------------------------------------------------------------------
CorrLtl == [] ( \A p \in correct : pc[p] = "InitReceived" => <> (pc[p] = "Accepted") )
RelayLtl == [] ( \E p \in correct : pc[p] = "Accepted" => <> ( \A q \in correct : pc[q] = "Accepted") )
UnforgLtl == [] ( \A p \in correct : pc[p] # "Accepted" )

\*--------------------------------------------------------------------
\* THEOREMS (optional, for TLC)
\*--------------------------------------------------------------------
THEOREM Spec => []Unforgeability

=============================================================================