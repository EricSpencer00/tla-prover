---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Definitions
\* ----------------------------------------------------------------------
Proc == 1 .. N

Message == [type : {"ECHO"}, sender : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, hasInit, sentEcho, accepted, recv, sent

vars == <<Correct, Faulty, hasInit, sentEcho, accepted, recv, sent>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoSenders(p) == { m.sender : m \in recv[p] }

CntEcho(p) == Cardinality(EchoSenders(p))

AllMessages == sent \cup { [type |-> "ECHO", sender |-> f] : f \in Faulty }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ hasInit \in [Proc -> BOOLEAN]
  /\ sentEcho = [p \in Proc |-> FALSE]
  /\ accepted = [p \in Proc |-> FALSE]
  /\ recv = [p \in Proc |-> {}]
  /\ sent = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* (1) Receive new messages (correct process may receive any subset of
\*     messages that have been sent by correct processes together with
\*     arbitrary messages from Byzantine processes)
Receive(p) ==
  /\ p \in Correct
  /\ LET possible == AllMessages
     IN
        /\ new \subseteq possible \ recv[p]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
  /\ UNCHANGED <<Correct, Faulty, hasInit, sentEcho, accepted, sent>>

\* (2) Process that initially has the INIT message: send ECHO and accept
InitSendAndAccept(p) ==
  /\ p \in Correct
  /\ hasInit[p]
  /\ ~sentEcho[p]
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ sentEcho' = [sentEcho EXCEPT ![p] = TRUE]
  /\ accepted' = [accepted EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<Correct, Faulty, hasInit, recv>>

\* (3) Receive >= N-2T but < N-T distinct ECHO messages: send ECHO
ThreshSend(p) ==
  /\ p \in Correct
  /\ ~sentEcho[p]
  /\ CntEcho(p) >= N - 2*T
  /\ CntEcho(p) <  N - T
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ sentEcho' = [sentEcho EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<Correct, Faulty, hasInit, accepted, recv>>

\* (4) Receive >= N-T distinct ECHO messages (has not sent yet):
\*     send ECHO and accept
ThreshSendAndAccept(p) ==
  /\ p \in Correct
  /\ ~sentEcho[p]
  /\ CntEcho(p) >= N - T
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ sentEcho' = [sentEcho EXCEPT ![p] = TRUE]
  /\ accepted' = [accepted EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<Correct, Faulty, hasInit, recv>>

\* (5) Already sent ECHO, now receive >= N-T distinct ECHO messages: accept
AcceptOnly(p) ==
  /\ p \in Correct
  /\ sentEcho[p]
  /\ CntEcho(p) >= N - T
  /\ ~accepted[p]
  /\ accepted' = [accepted EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<Correct, Faulty, hasInit, sentEcho, recv, sent>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Correct : Receive(p)
  \/ \E p \in Correct : InitSendAndAccept(p)
  \/ \E p \in Correct : ThreshSend(p)
  \/ \E p \in Correct : ThreshSendAndAccept(p)
  \/ \E p \in Correct : AcceptOnly(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Faulty = Proc \ Correct
  /\ Cardinality(Correct) = N - F
  /\ F <= T
  /\ N > 3 * T
  /\ hasInit \in [Proc -> BOOLEAN]
  /\ sentEcho \in [Proc -> BOOLEAN]
  /\ accepted \in [Proc -> BOOLEAN]
  /\ recv \in [Proc -> SUBSET Message]
  /\ sent \subseteq Message

FCConstraints ==
  /\ Cardinality(Correct) = N - F
  /\ Cardinality(Faulty) = F
  /\ F <= T
  /\ N > 3 * T

\* ----------------------------------------------------------------------
\* LTL Properties
\* ----------------------------------------------------------------------
\* Correctness: if all correct processes start with INIT, eventually all accept
CorrLtl ==
  ( /\ \A p \in Correct : hasInit[p] )
    => <> ( /\ \A p \in Correct : accepted[p] )

\* Relay: if some correct process accepts, eventually all correct accept
RelayLtl ==
  ( /\ \E p \in Correct : accepted[p] )
    => <> ( /\ \A p \in Correct : accepted[p] )

\* Unforgeability: if no correct process starts with INIT, then no correct ever accepts
UnforgLtl ==
  ( /\ \A p \in Correct : ~hasInit[p] )
    => [] ( /\ \A p \in Correct : ~accepted[p] )

=============================================================================