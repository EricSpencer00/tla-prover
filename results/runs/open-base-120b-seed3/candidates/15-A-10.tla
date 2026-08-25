---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process universe
\* ----------------------------------------------------------------------
Proc == 1 .. N

\* ----------------------------------------------------------------------
\* Message definition (only ECHO messages are used)
\* ----------------------------------------------------------------------
Message == [type : {"ECHO"}, from : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES correct, faulty, pc, recv, sent

vars == <<correct, faulty, pc, recv, sent>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoSenders(p) == { m.from : m \in recv[p] /\ m.type = "ECHO" }

AllCorrectAccept == \A p \in correct : pc[p] = "accept"
AnyCorrectAccept == \E p \in correct : pc[p] = "accept"
AllCorrectInit   == \A p \in correct : pc[p] = "init"
NoCorrectInit    == \A p \in correct : pc[p] = "noinit"

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ correct \subseteq Proc
  /\ Cardinality(correct) = N - F
  /\ faulty = Proc \ correct
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]
  /\ \A p \in correct : pc[p] \in {"init", "noinit"}
  /\ \A p \in faulty  : pc[p] = "faulty"

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* A correct process may receive any subset of the messages that have been
\* sent (by correct processes) together with any possible ECHO messages
\* that could have been sent by Byzantine processes.
Receive(p) ==
  /\ p \in correct
  /\ \E newMsgs \in SUBSET (sent \cup { [type |-> "ECHO", from |-> b] : b \in faulty }) :
        /\ newMsgs \cap recv[p] = {}
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
        /\ UNCHANGED <<correct, faulty, pc, sent>>

\* Send an ECHO message according to the protocol rules.
SendEcho(p) ==
  /\ p \in correct
  /\ pc[p] # "echo"
  /\ LET es == EchoSenders(p) IN
        \/ (pc[p] = "init")
        \/ (pc[p] = "noinit" /\ Cardinality(es) >= N - 2*T /\ Cardinality(es) < N - T)
        \/ (Cardinality(es) >= N - T)
  /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
  /\ pc'   = [pc EXCEPT ![p] = "echo"]
  /\ UNCHANGED <<correct, faulty, recv>>

\* Accept the broadcast according to the protocol rules.
Accept(p) ==
  /\ p \in correct
  /\ LET es == EchoSenders(p) IN
        \/ (pc[p] = "init")
        \/ (pc[p] = "noinit" /\ Cardinality(es) >= N - T)
        \/ (pc[p] = "echo"   /\ Cardinality(es) >= N - T)
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

\* Byzantine processes may arbitrarily send ECHO messages.
ByzSend ==
  /\ \E b \in faulty :
        /\ sent' = sent \cup { [type |-> "ECHO", from |-> b] }
        /\ UNCHANGED <<correct, faulty, pc, recv>>

Next ==
  \/ \E p \in Proc : Receive(p)
  \/ \E p \in Proc : SendEcho(p)
  \/ \E p \in Proc : Accept(p)
  \/ ByzSend

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ correct \subseteq Proc
  /\ faulty = Proc \ correct
  /\ \A p \in Proc : pc[p] \in {"noinit", "init", "echo", "accept", "faulty"}
  /\ \A p \in Proc : recv[p] \subseteq { [type |-> "ECHO", from |-> q] : q \in Proc }
  /\ sent \subseteq { [type |-> "ECHO", from |-> q] : q \in Proc }

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* ----------------------------------------------------------------------
\* Liveness properties (expressed as LTL formulas)
\* ----------------------------------------------------------------------
CorrLtl   == [] (AllCorrectInit => <> AllCorrectAccept)
RelayLtl  == [] (AnyCorrectAccept => <> AllCorrectAccept)
UnforgLtl == [] (NoCorrectInit => [] ~AnyCorrectAccept)

=============================================================================