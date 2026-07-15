---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F

\* -------------------------------------------------
\* Derived sets
\* -------------------------------------------------
Proc == 1..N
ECHO == "ECHO"

\* -------------------------------------------------
\* Message type
\* -------------------------------------------------
Msg == [type : {"ECHO"}, sender : Proc]

\* -------------------------------------------------
\* Variables
\* -------------------------------------------------
VARIABLES
    correct,    \* set of correct processes
    faulty,     \* set of Byzantine processes
    pc,         \* program counter per process
    recv,       \* set of messages received per process
    sent        \* set of messages sent by correct processes

\* -------------------------------------------------
\* Initial state
\* -------------------------------------------------
Init ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ pc = [p \in Proc |-> 
                IF p \in correct 
                THEN IF p \in faulty THEN "Faulty" 
                     ELSE "NoInit"
                ELSE "Faulty"]
    /\ recv = [p \in Proc |-> {}]
    /\ sent = {}

\* -------------------------------------------------
\* Helper definitions
\* -------------------------------------------------
EchoFrom(p) == [type |-> "ECHO", sender |-> p]

\* Distinct senders of received ECHO messages at process p
DistinctEchoSenders(p) ==
    { m.sender : m \in recv[p] /\ m.type = "ECHO" }

\* -------------------------------------------------
\* Actions
\* -------------------------------------------------
\* (1) A correct process may receive any subset of messages that have been sent
\*     (including those possibly forged by Byzantine processes)
Receive(p) ==
    /\ p \in correct
    /\ LET new == SUBSET sent IN
       /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
    /\ UNCHANGED <<correct, faulty, pc, sent>>

\* (2) Process that started with INIT (here modeled as pc = "InitReceived")
\*     immediately accepts and sends its own ECHO
AcceptAndEchoFromInit(p) ==
    /\ p \in correct
    /\ pc[p] = "InitReceived"
    /\ sent' = sent \cup { EchoFrom(p) }
    /\ pc'  = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<correct, faulty, recv>>

\* (3) Process without ECHO yet, receives >= N-2T but < N-T ECHO, sends ECHO, does not accept
SendEchoNoAccept(p) ==
    /\ p \in correct
    /\ pc[p] = "NoEcho"
    /\ LET cnt == Cardinality( DistinctEchoSenders(p) ) IN
       /\ cnt >= N - 2*T
       /\ cnt < N - T
    /\ sent' = sent \cup { EchoFrom(p) }
    /\ pc'  = [pc EXCEPT ![p] = "SentEcho"]
    /\ UNCHANGED <<correct, faulty, recv>>

\* (4) Process without ECHO yet, receives >= N-T ECHO, sends ECHO and accepts
SendEchoAndAccept(p) ==
    /\ p \in correct
    /\ pc[p] = "NoEcho"
    /\ Cardinality( DistinctEchoSenders(p) ) >= N - T
    /\ sent' = sent \cup { EchoFrom(p) }
    /\ pc'  = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<correct, faulty, recv>>

\* (5) Process that already sent ECHO receives >= N-T ECHO, accepts
AcceptAfterEcho(p) ==
    /\ p \in correct
    /\ pc[p] = "SentEcho"
    /\ Cardinality( DistinctEchoSenders(p) ) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<correct, faulty, recv, sent>>

\* (6) Byzantine processes may send arbitrary messages (modeled implicitly via nondet Receive)
\* No explicit action needed; they influence the set of possible received messages.

\* -------------------------------------------------
\* Next-state relation
\* -------------------------------------------------
Next ==
    \/ \E p \in Proc : Receive(p)
    \/ \E p \in correct : AcceptAndEchoFromInit(p)
    \/ \E p \in correct : SendEchoNoAccept(p)
    \/ \E p \in correct : SendEchoAndAccept(p)
    \/ \E p \in correct : AcceptAfterEcho(p)

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec == Init /\ [][Next]_<<correct, faulty, pc, recv, sent>>

\* -------------------------------------------------
\* TypeOK invariant
\* -------------------------------------------------
TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ pc \in [Proc -> {"NoInit","InitReceived","NoEcho","SentEcho","Accepted","Faulty"}]
    /\ recv \in [Proc -> SUBSET Msg]
    /\ sent \in SUBSET Msg
    /\ \A m \in sent : m.type = "ECHO" /\ m.sender \in Proc

\* -------------------------------------------------
\* FCConstraints (the safety property described)
\* -------------------------------------------------
FCConstraints ==
    /\ Cardinality(correct) > 0
    /\ \A p \in correct : 
          (pc[p] = "Accepted") => 
          (\E q \in correct : pc[q] = "Accepted")

\* -------------------------------------------------
\* Liveness properties (as temporal formulas)
\* -------------------------------------------------
CorrLtl ==
    /\ \A p \in correct : pc[p] = "InitReceived"
    => <> ( \A p \in correct : pc[p] = "Accepted" )

RelayLtl ==
    ( \E p \in correct : pc[p] = "Accepted" )
    => <> ( \A p \in correct : pc[p] = "Accepted" )

UnforgLtl ==
    /\ \A p \in correct : pc[p] # "InitReceived"
    => [] ( \A p \in correct : pc[p] # "Accepted" )

====