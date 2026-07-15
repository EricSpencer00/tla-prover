---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc == 1..N
MsgType == {"ECHO"}                \* only one message type in this model
Msg == [type : MsgType, sender : Proc]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    correct,       \* set of correct processes
    faulty,        \* set of Byzantine processes
    pc,            \* control location of each process
    sent,          \* set of messages sent by correct processes
    rcvd           \* set of messages received by each process

\* ----------------------------------------------------------------------
\* Enumerated control locations
\* ----------------------------------------------------------------------
PCValues == {"InitNo", "InitYes", "EchoSent", "Accepted"}

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoOf(p) == [type |-> "ECHO", sender |-> p]

EchoesFrom(S) == { m \in S : m.type = "ECHO" }

DistinctSenders(S) == { m.sender : m \in S }

NumEchosFrom(S, Snd) ==
    Cardinality({ m \in S : m.type = "ECHO" /\ m.sender \in Snd })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ pc \in [Proc -> PCValues]
    /\ sent = {}
    /\ rcvd = [p \in Proc |-> {}]
    /\ \A p \in correct:
          /\ pc[p] \in {"InitNo", "InitYes"}
          /\ IF pc[p] = "InitYes" THEN sent' = sent
          ELSE TRUE

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Receive(p) ==
    /\ p \in correct
    /\ \E newMsgs \subseteq (sent \cup { EchoOf(b) : b \in faulty }):
        /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup newMsgs]

SendEcho(p) ==
    /\ p \in correct
    /\ pc[p] = "EchoSent"
    /\ sent' = sent \cup { EchoOf(p) }
    /\ UNCHANGED << correct, faulty, pc, rcvd >>

Accept(p) ==
    /\ p \in correct
    /\ pc[p] \in {"EchoSent", "InitYes"}
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED << correct, faulty, sent, rcvd >>

InitialAccept(p) ==
    /\ p \in correct
    /\ pc[p] = "InitYes"
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = sent \cup { EchoOf(p) }
    /\ UNCHANGED << correct, faulty, rcvd >>

SendEchoIfNeeded(p) ==
    /\ p \in correct
    /\ pc[p] = "InitNo"
    /\ LET echos == EchoesFrom(rcvd[p]) IN
       /\ Cardinality(DistinctSenders(echos)) >= N - 2*T
       /\ Cardinality(DistinctSenders(echos)) < N - T
       /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
       /\ sent' = sent \cup { EchoOf(p) }
       /\ UNCHANGED << correct, faulty, rcvd >>

SendEchoAndAccept(p) ==
    /\ p \in correct
    /\ pc[p] = "InitNo"
    /\ LET echos == EchoesFrom(rcvd[p]) IN
       /\ Cardinality(DistinctSenders(echos)) >= N - T
       /\ pc' = [pc EXCEPT ![p] = "Accepted"]
       /\ sent' = sent \cup { EchoOf(p) }
       /\ UNCHANGED << correct, faulty, rcvd >>

AcceptAfterEcho(p) ==
    /\ p \in correct
    /\ pc[p] = "EchoSent"
    /\ LET echos == EchoesFrom(rcvd[p]) IN
       /\ Cardinality(DistinctSenders(echos)) >= N - T
       /\ pc' = [pc EXCEPT ![p] = "Accepted"]
       /\ UNCHANGED << correct, faulty, sent, rcvd >>

Next ==
    \/ \E p \in correct: Receive(p)
    \/ \E p \in correct: InitialAccept(p)
    \/ \E p \in correct: SendEchoIfNeeded(p)
    \/ \E p \in correct: SendEchoAndAccept(p)
    \/ \E p \in correct: AcceptAfterEcho(p)
    \/ \E p \in correct: SendEcho(p)       \* for continuation after EchoSent

Spec == Init /\ [][Next]_<<correct, faulty, pc, sent, rcvd>>

\* ----------------------------------------------------------------------
\* Type correctness (TypeOK) invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ pc \in [Proc -> PCValues]
    /\ sent \subseteq { EchoOf(p) : p \in Proc }
    /\ rcvd \in [Proc -> SUBSET { EchoOf(p) : p \in Proc }]

\* ----------------------------------------------------------------------
\* FCConstraints (the safety invariant described)
\* ----------------------------------------------------------------------
FCConstraints ==
    /\ \A p \in correct: pc[p] = "Accepted" => pc[p] = "Accepted"
    /\ \A p \in correct: pc[p] = "Accepted" => 
          Cardinality(DistinctSenders(rcvd[p])) >= N - T
    /\ \A p \in correct: pc[p] = "EchoSent" => 
          Cardinality(DistinctSenders(rcvd[p])) >= N - 2*T

\* ----------------------------------------------------------------------
\* Liveness properties (expressed as temporal formulas)
\* ----------------------------------------------------------------------
CorrLtl ==
    /\ \A p \in correct: pc[p] = "InitYes" => <> (pc[p] = "Accepted")

RelayLtl ==
    [] ( \E p \in correct: pc[p] = "Accepted"
         => <> (\A q \in correct: pc[q] = "Accepted") )

UnforgLtl ==
    ( \A p \in correct: pc[p] = "InitNo" )
    => [] ( \A p \in correct: pc[p] # "Accepted" )

\* ----------------------------------------------------------------------
\* THEOREMS (optional, for TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []FCConstraints
THEOREM Spec => CorrLtl
THEOREM Spec => RelayLtl
THEOREM Spec => UnforgLtl

====