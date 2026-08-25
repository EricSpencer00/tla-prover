---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Types and basic sets
\* ----------------------------------------------------------------------
Proc == 1..N
Msg  == [type : {"ECHO"}, from : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, sent, recv

vars == <<Correct, Faulty, pc, sent, recv>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ByzMsgs == { [type |-> "ECHO", from |-> q] : q \in Faulty }

EchoFrom(p) == { m.from : m \in recv[p] /\ m.type = "ECHO" }

SentEcho(p) == [type |-> "ECHO", from |-> p] \in sent

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ \A p \in Correct : pc[p] \in {"InitRecv", "NoInit"}
  /\ \A p \in Faulty   : pc[p] = "Byz"
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* One combined receive‑and‑act step for a correct process p
\* ----------------------------------------------------------------------
ReceiveAct(p) ==
  LET newMsgs == ANY S \in SUBSET (sent \cup ByzMsgs) \ 
                    : S \subseteq (sent \cup ByzMsgs) \ (recv[p])
  IN
    /\ p \in Correct
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
    /\ CASE 
        /\ pc[p] = "InitRecv" ->
           /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
           /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
        /\ pc[p] = "NoInit" /\ ~SentEcho(p) /\ Cardinality(EchoFrom(p)) >= N - 2*T 
                         /\ Cardinality(EchoFrom(p)) <  N - T ->
           /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
           /\ pc'   = [pc EXCEPT ![p] = "EchoSent"]
        /\ pc[p] = "NoInit" /\ ~SentEcho(p) /\ Cardinality(EchoFrom(p)) >= N - T ->
           /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
           /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
        /\ pc[p] = "EchoSent" /\ Cardinality(EchoFrom(p)) >= N - T ->
           /\ sent' = sent
           /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
        /\ OTHER ->
           /\ sent' = sent
           /\ pc'   = pc
    /\ UNCHANGED <<Correct, Faulty>>

Next ==
  \/ \E p \in Correct : ReceiveAct(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Faulty   = Proc \ Correct
  /\ \A p \in Proc : pc[p] \in {"InitRecv", "NoInit", "EchoSent", "Accepted", "Byz"}
  /\ sent \subseteq Msg
  /\ \A p \in Proc : recv[p] \subseteq Msg

\* ----------------------------------------------------------------------
\* Fault‑tolerance constraints
\* ----------------------------------------------------------------------
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(Correct) = N - F

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
\* (1) Correctness: if every correct process starts having received the INIT,
\*     then eventually all correct processes accept.
CorrLtl ==
  [] ( ( \A p \in Correct : pc[p] = "InitRecv" ) => <> ( \A p \in Correct : pc[p] = "Accepted" ) )

\* (2) Relay: once some correct process accepts, eventually all correct accept.
RelayLtl ==
  [] ( ( \E p \in Correct : pc[p] = "Accepted" ) => <> ( \A p \in Correct : pc[p] = "Accepted" ) )

\* (3) Unforgeability: if no correct process starts with the INIT,
\*     then no correct process ever accepts.
UnforgLtl ==
  [] ( ( \A p \in Correct : pc[p] # "InitRecv" ) => [] ( \A p \in Correct : pc[p] # "Accepted" ) )

=============================================================================