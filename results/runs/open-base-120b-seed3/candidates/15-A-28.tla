---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process identifiers
\* ----------------------------------------------------------------------
Proc == 1 .. N

\* ----------------------------------------------------------------------
\* Message type (only ECHO)
\* ----------------------------------------------------------------------
Msg == [sender : Proc, mtype : {"ECHO"}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, sent, recv

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
DistinctSenders(S) == { m.sender : m \in S }
NumDistinctSenders(S) == Cardinality(DistinctSenders(S))

SendEchoMsg(p) == [sender |-> p, mtype |-> "ECHO"]

ByzMsgs == { [sender |-> b, mtype |-> "ECHO"] : b \in Faulty }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]
  /\ \E initSet \subseteq Correct :
        /\ \A p \in Correct : pc[p] = (IF p \in initSet THEN "Init1" ELSE "Init0")
        /\ \A p \in Faulty : pc[p] = "Init0"

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Receive arbitrary new messages (including from Byzantine processes)
Receive(p) ==
  /\ p \in Correct
  /\ \E new \subseteq (sent \cup ByzMsgs) \ setminus recv[p] :
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
        /\ UNCHANGED <<Correct, Faulty, pc, sent>>

\* 2. Immediate accept and echo when the process started with INIT
InitAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "Init1"
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ sent' = sent \cup { SendEchoMsg(p) }
  /\ UNCHANGED <<Correct, Faulty, recv>>

\* 3. Send ECHO (but not accept) when enough ECHO messages received
EchoLess(p) ==
  /\ p \in Correct
  /\ pc[p] = "Init0"
  /\ NumDistinctSenders(recv[p]) >= N - 2 * T
  /\ NumDistinctSenders(recv[p]) <  N - T
  /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
  /\ sent' = sent \cup { SendEchoMsg(p) }
  /\ UNCHANGED <<Correct, Faulty, recv>>

\* 4. Send ECHO (if not already sent) and accept when enough ECHO messages received
EchoAccept(p) ==
  /\ p \in Correct
  /\ pc[p] \in {"Init0", "EchoSent"}
  /\ NumDistinctSenders(recv[p]) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ IF pc[p] = "Init0"
        THEN sent' = sent \cup { SendEchoMsg(p) }
        ELSE sent' = sent
  /\ UNCHANGED <<Correct, Faulty, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Correct : Receive(p)
    \/ \E p \in Correct : InitAccept(p)
    \/ \E p \in Correct : EchoLess(p)
    \/ \E p \in Correct : EchoAccept(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Vars == <<Correct, Faulty, pc, sent, recv>>
Spec == Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> {"Init0", "Init1", "EchoSent", "Accepted"}]
  /\ sent \subseteq { [sender : Proc, mtype : {"ECHO"}] }
  /\ recv \in [Proc -> SUBSET { [sender : Proc, mtype : {"ECHO"}] }]

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* ----------------------------------------------------------------------
\* Temporal properties (LTL style)
\* ----------------------------------------------------------------------
AllCorrectAccepted == \A p \in Correct : pc[p] = "Accepted"
AllCorrectInit     == \A p \in Correct : pc[p] = "Init1"
AllCorrectNoInit   == \A p \in Correct : pc[p] = "Init0"

CorrLtl   == (Init /\ AllCorrectInit) => <> AllCorrectAccepted
RelayLtl  == [] ( (\E p \in Correct : pc[p] = "Accepted") => <> AllCorrectAccepted )
UnforgLtl == (Init /\ AllCorrectNoInit) => [] ( \A p \in Correct : pc[p] # "Accepted" )

\* ----------------------------------------------------------------------
\* THE END
\* ----------------------------------------------------------------------
====