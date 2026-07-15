---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
PROC == 1..N

\* ----------------------------------------------------------------------
\* Message type
\* ----------------------------------------------------------------------
MessageType == {"ECHO"}

Msg == [type : MessageType, sender : PROC]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    correct,      \* set of correct processes
    faulty,       \* set of faulty processes
    pc,           \* control location of each process
    sent,         \* set of ECHO messages that have been sent by correct processes
    recv          \* mapping proc -> set of messages it has received

\* ----------------------------------------------------------------------
\* Control locations
\* ----------------------------------------------------------------------
PcVals == {"InitNo", "InitYes", "SentEcho", "Accepted"}

\* ----------------------------------------------------------------------
\* Initial state (any correct process may or may not have received INIT)
\* ----------------------------------------------------------------------
Init ==
    /\ correct \subseteq PROC
    /\ Cardinality(correct) = N - F
    /\ faulty = PROC \ correct
    /\ pc \in [PROC -> PcVals]
    /\ \A p \in PROC :
          pc[p] \in {"InitNo", "InitYes"}
    /\ sent = {}
    /\ recv = [p \in PROC |-> {}]

\* ----------------------------------------------------------------------
\* Derived predicates
\* ----------------------------------------------------------------------
EchoCount(p) == Cardinality({ m \in recv[p] : m.type = "ECHO" })
DistinctEchoSenders(p) ==
    { m.sender : m \in recv[p] /\ m.type = "ECHO" }

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Receive any subset of messages that have been sent by correct processes
\*    plus arbitrary messages from faulty processes (simulated by any sender
\*    in faulty).
Receive(p) ==
    /\ pc[p] # "Accepted"
    /\ LET possible == sent \cup { [type |-> "ECHO", sender |-> f] :
                              f \in faulty }
       IN recv' = [recv EXCEPT ![p] = recv[p] \cup SUBSET possible]
    /\ UNCHANGED <<correct, faulty, pc, sent>>

\* 2. If a process started with INIT, it immediately accepts and sends ECHO
InitAcceptAndEcho(p) ==
    /\ pc[p] = "InitYes"
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
    /\ UNCHANGED <<correct, faulty, recv>>

\* 3. Process that has not sent ECHO yet receives at least N-2T distinct ECHOs,
\*    sends its own ECHO but does not accept.
SendEchoNoAccept(p) ==
    /\ pc[p] \in {"InitNo", "SentEcho"}    \* not yet accepted
    /\ EchoCount(p) >= N - 2*T
    /\ EchoCount(p) < N - T
    /\ pc[p] # "SentEcho"                  \* ensure we send only once
    /\ pc' = [pc EXCEPT ![p] = "SentEcho"]
    /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
    /\ UNCHANGED <<correct, faulty, recv>>

\* 4. Process receives at least N-T distinct ECHOs, sends ECHO and accepts.
SendEchoAndAccept(p) ==
    /\ pc[p] \in {"InitNo", "SentEcho"}    \* not yet accepted
    /\ EchoCount(p) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
    /\ UNCHANGED <<correct, faulty, recv>>

\* 5. Process that already sent ECHO receives >= N-T distinct ECHOs and accepts.
AcceptAfterEcho(p) ==
    /\ pc[p] = "SentEcho"
    /\ EchoCount(p) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<correct, faulty, sent, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in correct :
        \/ Receive(p)
        \/ InitAcceptAndEcho(p)
        \/ SendEchoNoAccept(p)
        \/ SendEchoAndAccept(p)
        \/ AcceptAfterEcho(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<correct, faulty, pc, sent, recv>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
\* TypeOK: all variables stay within their domains
TypeOK ==
    /\ correct \subseteq PROC
    /\ Cardinality(correct) = N - F
    /\ faulty = PROC \ correct
    /\ pc \in [PROC -> PcVals]
    /\ sent \subseteq { [type |-> "ECHO", sender |-> p] : p \in correct }
    /\ recv \in [PROC -> SUBSET Msg]

\* FCConstraints: the main safety property described in the text.
\* If no correct process started with the broadcast (InitYes), then no
\* correct process ever reaches the Accepted state.
FCConstraints ==
    ( \A p \in correct : pc[p] # "InitYes" ) =>
    ( \A p \in correct : pc[p] # "Accepted" )

\* ----------------------------------------------------------------------
\* Liveness properties (expressed as invariants for TLC)
\* ----------------------------------------------------------------------
\* CorrLtl: if all correct processes start with InitYes, eventually all accept
CorrLtl ==
    ( \A p \in correct : pc[p] = "InitYes" )
    => <> ( \A p \in correct : pc[p] = "Accepted" )

\* RelayLtl: if any correct process accepts, eventually all accept
RelayLtl ==
    ( \E p \in correct : pc[p] = "Accepted" )
    => <> ( \A p \in correct : pc[p] = "Accepted" )

\* UnforgLtl: the safety property expressed as a temporal property
UnforgLtl ==
    [] ( ( \A p \in correct : pc[p] # "InitYes" ) => ( \A p \in correct : pc[p] # "Accepted" ) )

====