---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT N, T, F

\*--------------------------------------------------------------------
\* Derived sets
\*--------------------------------------------------------------------
Proc == 1..N
ECHO == {"ECHO"}

\* Message is a pair <<sender, type>>
Msg == [sender : Proc, type : {"ECHO"}]

\*--------------------------------------------------------------------
\* Type definitions
\*--------------------------------------------------------------------
PCValues == {"init_no", "init_yes", "sent_echo", "accept"}

\*--------------------------------------------------------------------
\* Variables
\*--------------------------------------------------------------------
VARIABLES
    correct,        \* Set of correct processes
    faulty,         \* Set of Byzantine processes
    pc,             \* Process control state: [proc -> PCValues]
    sent,           \* Set of messages sent by correct processes
    recvd           \* Messages received by each process: [proc -> SUBSET Msg]

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
SentByCorrect == { m \in sent : m.sender \in correct }

EchosFromCorrect(p) == { m.sender : 
        \E m \in SentByCorrect : m.type = "ECHO" /\ m.sender # p }

\* A message of type ECHO from a Byzantine sender is always possible,
\* but we never enumerate them explicitly; they are implicitly allowed
\* when a Byzantine process chooses to send.

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ pc = [p \in Proc |-> IF p \in correct THEN "init_no" ELSE "init_yes"]
       \* Non‑broadcast case: all correct start with "init_no"
    /\ sent = {}
    /\ recvd = [p \in Proc |-> {}]

\*--------------------------------------------------------------------
\* Actions
\*--------------------------------------------------------------------
\* 1. Receive any subset of messages that have been sent (including possible
\*    Byzantine messages that are not tracked in 'sent')
Recv(p) ==
    /\ p \in Proc
    /\ UNCHANGED <<correct, faulty, pc, sent>>
    /\ recvd' = [recvd EXCEPT ![p] = recvd[p] \cup
                CHOOSE msgs \in SUBSET (SentByCorrect \cup
                    { [sender |-> b, type |-> "ECHO"] :
                        b \in faulty })
                : TRUE]

\* 2. Immediate accept and send ECHO after having received INIT (init_yes)
AcceptAndEchoInit(p) ==
    /\ p \in correct
    /\ pc[p] = "init_yes"
    /\ let newMsg == [sender |-> p, type |-> "ECHO"] in
       /\ sent' = sent \cup {newMsg}
       /\ pc' = [pc EXCEPT ![p] = "accept"]
       /\ UNCHANGED recvd

\* 3. Send ECHO when received >= N-2T distinct ECHO messages (but < N-T)
SendEchoMid(p) ==
    /\ p \in correct
    /\ pc[p] = "init_no"
    /\ LET cnt == Cardinality(EchosFromCorrect(p)) IN
       /\ cnt >= N - 2 * T
       /\ cnt < N - T
    /\ let newMsg == [sender |-> p, type |-> "ECHO"] in
       /\ sent' = sent \cup {newMsg}
       /\ pc' = [pc EXCEPT ![p] = "sent_echo"]
       /\ UNCHANGED recvd

\* 4. Send ECHO and accept when received >= N-T distinct ECHO messages
SendEchoAndAccept(p) ==
    /\ p \in correct
    /\ pc[p] \in {"init_no", "sent_echo"}
    /\ Cardinality(EchosFromCorrect(p)) >= N - T
    /\ LET newMsg == [sender |-> p, type |-> "ECHO"] IN
       /\ sent' = sent \cup {newMsg}
       /\ pc' = [pc EXCEPT ![p] = "accept"]
       /\ UNCHANGED recvd

\* 5. Accept after already having sent ECHO and now receiving >= N-T ECHOs
AcceptAfterEcho(p) ==
    /\ p \in correct
    /\ pc[p] = "sent_echo"
    /\ Cardinality(EchosFromCorrect(p)) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "accept"]
    /\ UNCHANGED <<sent, recvd>>

\* 6. Byzantine process may send any ECHO messages (non‑deterministic)
ByzSend(p) ==
    /\ p \in faulty
    /\ \E m \in Msg : m.type = "ECHO" /\ m.sender = p
    /\ UNCHANGED <<correct, pc, sent, recvd>>

\* Composite step for a correct process
CorrectStep(p) ==
    \/ Recv(p)
    \/ AcceptAndEchoInit(p)
    \/ SendEchoMid(p)
    \/ SendEchoAndAccept(p)
    \/ AcceptAfterEcho(p)

\* Global next-state relation
Next ==
    \/ \E p \in Proc : CorrectStep(p)
    \/ \E p \in faulty : ByzSend(p)

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<correct, faulty, pc, sent, recvd>>

\*--------------------------------------------------------------------
\* Type correctness invariant
\*--------------------------------------------------------------------
TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ pc \in [Proc -> PCValues]
    /\ sent \subseteq SentByCorrect
    /\ \A p \in Proc : recvd[p] \subseteq Msg

\*--------------------------------------------------------------------
\* Fault‑containment invariant (matches the description's "FCConstraints")
\*--------------------------------------------------------------------
FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\*--------------------------------------------------------------------
\* Liveness properties
\*--------------------------------------------------------------------
UnforgLtl == []<>(\A p \in correct : pc[p] # "accept")
CorrLtl   == []<>(\A p \in correct : pc[p] = "init_yes") => <> (\A p \in correct : pc[p] = "accept")
RelayLtl  == [](\E p \in correct : pc[p] = "accept") => <> (\A p \in correct : pc[p] = "accept")

====