---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS N, T, F

VARIABLES Correct, Faulty, pc, sent, recv, InitSet

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of all process identifiers
ProcSet == 1..N

\* Control locations for correct processes
PCVals == {"NoInit", "Init", "Echo", "Accept"}

\* Message is simply the sender identifier (ECHO messages only)
Msg == ProcSet

\* Number of distinct ECHO messages received by p
EchoCount(p) == Cardinality(recv[p])

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Correct \subseteq ProcSet
  /\ Cardinality(Correct) = N - F
  /\ Faulty = ProcSet \ Correct
  /\ InitSet \subseteq Correct
  /\ pc = [p \in ProcSet |-> IF p \in InitSet THEN "Init" ELSE "NoInit"]
  /\ sent = {}
  /\ recv = [p \in ProcSet |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* A correct process that starts with the INIT message immediately
\* accepts and sends an ECHO.
InitAct(p) ==
  /\ p \in Correct
  /\ pc[p] = "Init"
  /\ pc' = [pc EXCEPT ![p] = "Accept"]
  /\ sent' = sent \cup {p}
  /\ UNCHANGED <<recv, Correct, Faulty, InitSet>>

\* A correct process may receive any subset of messages that have been
\* sent by correct processes together with arbitrary messages from
\* Byzantine processes.
Receive(p) ==
  /\ p \in Correct
  /\ \E newMsgs \in SUBSET (Correct \cup Faulty) :
        /\ newMsgs \subseteq (sent \cup Faulty)
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
  /\ UNCHANGED <<pc, sent, Correct, Faulty, InitSet>>

\* A correct process that has not yet sent ECHO sends it after receiving
\* at least N-2T distinct ECHO messages but fewer than N-T.
SendEcho(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ EchoCount(p) >= N - 2 * T
  /\ EchoCount(p) < N - T
  /\ pc' = [pc EXCEPT ![p] = "Echo"]
  /\ sent' = sent \cup {p}
  /\ UNCHANGED <<recv, Correct, Faulty, InitSet>>

\* A correct process that has not yet sent ECHO sends it and accepts
\* after receiving at least N-T distinct ECHO messages.
SendEchoAndAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ EchoCount(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accept"]
  /\ sent' = sent \cup {p}
  /\ UNCHANGED <<recv, Correct, Faulty, InitSet>>

\* A correct process that has already sent ECHO accepts after receiving
\* at least N-T distinct ECHO messages.
AcceptAfterEcho(p) ==
  /\ p \in Correct
  /\ pc[p] = "Echo"
  /\ EchoCount(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accept"]
  /\ UNCHANGED <<recv, sent, Correct, Faulty, InitSet>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Correct: InitAct(p)
  \/ \E p \in Correct: Receive(p)
  \/ \E p \in Correct: SendEcho(p)
  \/ \E p \in Correct: SendEchoAndAccept(p)
  \/ \E p \in Correct: AcceptAfterEcho(p)

vars == <<Correct, Faulty, pc, sent, recv, InitSet>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq ProcSet
  /\ Cardinality(Correct) = N - F
  /\ Faulty = ProcSet \ Correct
  /\ InitSet \subseteq Correct
  /\ pc \in [ProcSet -> PCVals]
  /\ sent \subseteq Correct
  /\ recv \in [ProcSet -> SUBSET (Correct \cup Faulty)]

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl == [] ( ( \A p \in Correct: pc[p] = "Init") => <> ( \A p \in Correct: pc[p] = "Accept") )

RelayLtl == [] ( ( \E p \in Correct: pc[p] = "Accept") => <> ( \A p \in Correct: pc[p] = "Accept") )

UnforgLtl == [] ( ( \A p \in Correct: pc[p] = "NoInit") => [] ( \A p \in Correct: pc[p] # "Accept") )
=============================================================================