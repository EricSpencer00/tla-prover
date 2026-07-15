---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
VARIABLES
    correct,               \* Set of correct processes
    faulty,                \* Set of Byzantine processes
    pc,                    \* Control location per process
    sent,                  \* Set of ECHO messages sent by correct processes
    recv,                  \* Set of messages received by each process
    accepted               \* Set of processes that have accepted

\* ----------------------------------------------------------------------
\* Constants constraints (derived from the description)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ N \in Nat
    /\ T \in Nat
    /\ F \in Nat
    /\ N > 3 * T
    /\ F <= T
    /\ F >= 0

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Message == [type : {"ECHO"}, sender : 1..N]

CInit   == "Init"        \* Process has received INIT and has not yet sent ECHO
CWait   == "Wait"        \* Process waiting to collect ECHO messages
CSent   == "Sent"        \* Process has sent ECHO but not yet accepted
CAcc    == "Acc"         \* Process has accepted
FProc   == "Faulty"      \* Control location for Byzantine processes (unused but kept for completeness)

AllProcs == 1..N

SentByCorrect(msg) ==
    /\ msg.type = "ECHO"
    /\ msg.sender \in correct
    /\ msg \in sent

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ TypeOK
    /\ correct \subseteq AllProcs
    /\ faulty = AllProcs \ correct
    /\ Cardinality(correct) = N - F
    /\ pc = [p \in AllProcs |-> IF p \in correct THEN CWait ELSE FProc]
    /\ sent = {}
    /\ recv = [p \in AllProcs |-> {}]
    /\ accepted = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* (1) Receive new messages
Recv(p) ==
    /\ p \in correct
    /\ \E newMsgs \subseteq (sent \cup
          { [type |-> "ECHO", sender |-> b] : b \in faulty })
       : /\ recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
          /\ UNCHANGED <<correct, faulty, pc, sent, accepted>>

\* (2) Immediate accept after receiving INIT (modeled as starting in CInit)
ImmediateAccept(p) ==
    /\ p \in correct
    /\ pc[p] = CInit
    /\ pc' = [pc EXCEPT ![p] = CAcc]
    /\ accepted' = accepted \cup {p}
    /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
    /\ UNCHANGED <<correct, faulty, recv>>

\* (3) Send ECHO after receiving >= N-2T but < N-T ECHO messages
SendEcho_Weak(p) ==
    /\ p \in correct
    /\ pc[p] = CWait
    /\ Cardinality({ m \in recv[p] : m.type = "ECHO" }) >= N - 2 * T
    /\ Cardinality({ m \in recv[p] : m.type = "ECHO" }) < N - T
    /\ pc' = [pc EXCEPT ![p] = CSent]
    /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
    /\ UNCHANGED <<correct, faulty, recv, accepted>>

\* (4) Send ECHO and accept after receiving >= N-T ECHO messages (first time)
SendEchoAndAccept(p) ==
    /\ p \in correct
    /\ pc[p] = CWait
    /\ Cardinality({ m \in recv[p] : m.type = "ECHO" }) >= N - T
    /\ pc' = [pc EXCEPT ![p] = CAcc]
    /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
    /\ accepted' = accepted \cup {p}
    /\ UNCHANGED <<correct, faulty, recv>>

\* (5) Accept after already sent ECHO and receiving >= N-T distinct ECHO messages
AcceptAfterEcho(p) ==
    /\ p \in correct
    /\ pc[p] = CSent
    /\ Cardinality({ m \in recv[p] : m.type = "ECHO" }) >= N - T
    /\ pc' = [pc EXCEPT ![p] = CAcc]
    /\ accepted' = accepted \cup {p}
    /\ UNCHANGED <<correct, faulty, recv, sent>>

\* (6) Byzantine processes may send arbitrary ECHO messages
ByzSend(p) ==
    /\ p \in faulty
    /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
    /\ UNCHANGED <<correct, faulty, pc, recv, accepted>>

\* (7) No‑op for all other cases
NoOp ==
    UNCHANGED <<correct, faulty, pc, sent, recv, accepted>>

Next ==
    \/ \E p \in correct : Recv(p)
    \/ \E p \in correct : ImmediateAccept(p)
    \/ \E p \in correct : SendEcho_Weak(p)
    \/ \E p \in correct : SendEchoAndAccept(p)
    \/ \E p \in correct : AcceptAfterEcho(p)
    \/ \E p \in faulty  : ByzSend(p)
    \/ NoOp

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<correct, faulty, pc, sent, recv, accepted>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
\* Type safety (states stay within their domains)
DomainInv ==
    /\ correct \subseteq AllProcs
    /\ faulty = AllProcs \ correct
    /\ pc \in [AllProcs -> {"Init","Wait","Sent","Acc","Faulty"}]
    /\ sent \subseteq { [type |-> "ECHO", sender |-> i] : i \in correct }
    /\ recv \in [AllProcs -> SUBSET sent \cup
                { [type |-> "ECHO", sender |-> i] : i \in faulty }]
    /\ accepted \subseteq correct

\* FCConstraints corresponds to the safety property Unforgeability
FCConstraints ==
    /\ ( \A p \in correct : pc[p] = CInit ) => ( \A p \in correct : pc[p] = CAcc )
    /\ ( \A p \in correct : pc[p] = CWait ) => ( \A p \in correct : pc[p] = CWait )

\* ----------------------------------------------------------------------
\* Liveness properties
\* ----------------------------------------------------------------------
CorrLtl ==
    ( \A p \in correct : pc[p] = CInit ) => []<>( \A p \in correct : pc[p] = CAcc )

RelayLtl ==
    ( \E p \in correct : pc[p] = CAcc ) => []<>( \A p \in correct : pc[p] = CAcc )

UnforgLtl ==
    ( \A p \in correct : pc[p] = CWait ) => []<>( \A p \in correct : pc[p] = CWait )

=============================================================================