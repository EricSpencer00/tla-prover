---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1..N

\* ----------------------------------------------------------------------
\* Message type
\* ----------------------------------------------------------------------
MsgType == {"ECHO"}

\* A message is a pair <<sender, type>>
Msg == [sender : Proc, type : MsgType]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    correct,        \* set of correct processes
    faulty,         \* set of Byzantine processes
    pc,             \* control location of each process
    recv,           \* set of messages received by each process
    sent             \* set of messages sent by correct processes

\* ----------------------------------------------------------------------
\* Control locations
\* ----------------------------------------------------------------------
PCVals == {"InitNo", "InitYes", "EchoSent", "Accepted"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ pc \in [Proc -> PCVals]
    /\ \A p \in Proc :
          pc[p] \in {"InitNo", "InitYes"}
    /\ recv = [p \in Proc |-> {}]
    /\ sent = {}

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoFrom(p) == [sender |-> p, type |-> "ECHO"]

EchoSet(p) == { m \in recv[p] : m.type = "ECHO" }

DistinctSenders(S) == { m.sender : m \in S }

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Receive new messages (any subset of sent plus any arbitrary Byzantine messages)
Receive(p) ==
    /\ p \in correct
    /\ \E new \subseteq (sent \cup { [sender |-> b, type |-> "ECHO"] : b \in faulty }) :
         /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
         /\ UNCHANGED <<correct, faulty, pc, sent>>

\* 2. If a process started with INIT, it immediately accepts and sends ECHO
InitAccept(p) ==
    /\ p \in correct
    /\ pc[p] = "InitYes"
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = sent \cup { EchoFrom(p) }
    /\ UNCHANGED <<correct, faulty, recv>>

\* 3. If a process that has not yet sent ECHO receives >= N-2T ECHO but < N-T, it sends ECHO (no accept)
EchoMid(p) ==
    /\ p \in correct
    /\ pc[p] = "InitNo"
    /\ LET eSet == EchoSet(p) IN
       /\ Cardinality(DistinctSenders(eSet)) >= N - 2*T
       /\ Cardinality(DistinctSenders(eSet)) < N - T
    /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
    /\ sent' = sent \cup { EchoFrom(p) }
    /\ UNCHANGED <<correct, faulty, recv>>

\* 4. If a process that has not yet sent ECHO receives >= N-T ECHO, it sends ECHO and accepts
EchoAndAccept(p) ==
    /\ p \in correct
    /\ pc[p] = "InitNo"
    /\ Cardinality(DistinctSenders(EchoSet(p))) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = sent \cup { EchoFrom(p) }
    /\ UNCHANGED <<correct, faulty, recv>>

\* 5. If a process already sent ECHO receives >= N-T ECHO, it accepts
AcceptAfterEcho(p) ==
    /\ p \in correct
    /\ pc[p] = "EchoSent"
    /\ Cardinality(DistinctSenders(EchoSet(p))) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<correct, faulty, recv, sent>>

\* 6. No-op for faulty processes (they may behave arbitrarily, but we model them as stuttering)
Stutter ==
    UNCHANGED <<correct, faulty, pc, recv, sent>>

Next ==
    \/ \E p \in correct : Receive(p)
    \/ \E p \in correct : InitAccept(p)
    \/ \E p \in correct : EchoMid(p)
    \/ \E p \in correct : EchoAndAccept(p)
    \/ \E p \in correct : AcceptAfterEcho(p)
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<correct, faulty, pc, recv, sent>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ pc \in [Proc -> PCVals]
    /\ \A p \in Proc : pc[p] \in PCVals
    /\ recv \in [Proc -> SUBSET Msg]
    /\ sent \subseteq Msg
    /\ \A m \in sent : m.type = "ECHO"
    /\ \A p \in Proc : \A m \in recv[p] : m.type = "ECHO"

\* ----------------------------------------------------------------------
\* Safety constraint: no correct process accepts if none started with INIT
\* ----------------------------------------------------------------------
FCConstraints ==
    ( \A p \in correct : pc[p] # "Accepted" )
    \/ ( \E p \in correct : pc[p] = "InitYes" )

\* ----------------------------------------------------------------------
\* Liveness properties (expressed as temporal formulas)
\* ----------------------------------------------------------------------
CorrLtl == 
    ( \A p \in correct : pc[p] = "InitYes" ) => <> ( \A p \in correct : pc[p] = "Accepted" )

RelayLtl ==
    ( \E p \in correct : pc[p] = "Accepted" ) => <> ( \A p \in correct : pc[p] = "Accepted" )

UnforgLtl ==
    ( \A p \in correct : pc[p] = "InitNo" ) => [] ( \A p \in correct : pc[p] # "Accepted" )

====