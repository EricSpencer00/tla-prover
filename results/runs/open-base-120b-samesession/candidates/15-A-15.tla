---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process universe
\* ----------------------------------------------------------------------
Proc == 1..N

\* ----------------------------------------------------------------------
\* Message definition (only ECHO messages)
\* ----------------------------------------------------------------------
Message == [type : {"ECHO"}, sender : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES correctSet, faultySet, pc, recv, sent

vars == << correctSet, faultySet, pc, recv, sent >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoSenders(p) == { m.sender : m \in recv[p] /\ m.type = "ECHO" }
EchoCount(p)   == Cardinality( EchoSenders(p) )

ByzantineMsgs == { [type |-> "ECHO", sender |-> b] : b \in faultySet }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ correctSet \in SUBSET Proc
  /\ Cardinality(correctSet) = N - F
  /\ faultySet = Proc \ correctSet
  /\ pc \in [Proc -> {"StartNo", "StartYes"}]
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* (1) Receive new messages (including possible Byzantine messages)
Receive(p) ==
  /\ p \in correctSet
  /\ LET possible == sent \cup ByzantineMsgs IN
       \E new \in SUBSET possible :
         /\ new \cap recv[p] = {}
         /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
         /\ UNCHANGED <<correctSet, faultySet, pc, sent>>

\* (2) Process a correct process that initially has the INIT message
InitAccept(p) ==
  /\ p \in correctSet
  /\ pc[p] = "StartYes"
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ UNCHANGED <<correctSet, faultySet, recv>>

\* (3) Send ECHO but do not yet accept (N-2T ≤ count < N-T)
EchoSendNoAccept(p) ==
  /\ p \in correctSet
  /\ pc[p] = "StartNo"
  /\ EchoCount(p) >= N - 2*T
  /\ EchoCount(p) < N - T
  /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ UNCHANGED <<correctSet, faultySet, recv>>

\* (4) Send ECHO and accept immediately (count ≥ N-T)
EchoSendAccept(p) ==
  /\ p \in correctSet
  /\ pc[p] = "StartNo"
  /\ EchoCount(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ UNCHANGED <<correctSet, faultySet, recv>>

\* (5) Already sent ECHO, now accept (count ≥ N-T)
AcceptAfterEcho(p) ==
  /\ p \in correctSet
  /\ pc[p] = "EchoSent"
  /\ EchoCount(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<correctSet, faultySet, recv, sent>>

Next ==
  \/ \E p \in Proc : Receive(p)
  \/ \E p \in Proc : InitAccept(p)
  \/ \E p \in Proc : EchoSendNoAccept(p)
  \/ \E p \in Proc : EchoSendAccept(p)
  \/ \E p \in Proc : AcceptAfterEcho(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ correctSet \in SUBSET Proc
  /\ faultySet = Proc \ correctSet
  /\ pc \in [Proc -> {"StartNo","StartYes","EchoSent","Accepted"}]
  /\ sent \subseteq Message
  /\ \A m \in sent : m.sender \in correctSet
  /\ recv \in [Proc -> SUBSET Message]
  /\ \A p \in Proc : \A m \in recv[p] : m \in Message

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(correctSet) = N - F
  /\ Cardinality(faultySet) = F

\* ----------------------------------------------------------------------
\* Temporal properties
\* ----------------------------------------------------------------------
\* All correct processes start with INIT -> eventually all accept
CorrLtl ==
  ( \A p \in correctSet : pc[p] = "StartYes" )
    => <> ( \A p \in correctSet : pc[p] = "Accepted" )

\* If any correct process accepts, eventually all accept
RelayLtl ==
  ( \E p \in correctSet : pc[p] = "Accepted" )
    => <> ( \A p \in correctSet : pc[p] = "Accepted" )

\* Unforgeability: if no correct process starts with INIT, never accept
UnforgLtl ==
  ( \A p \in correctSet : pc[p] = "StartNo" )
    => [] ( \A p \in correctSet : pc[p] # "Accepted" )

\* ----------------------------------------------------------------------
\* THE END
\* ----------------------------------------------------------------------
====