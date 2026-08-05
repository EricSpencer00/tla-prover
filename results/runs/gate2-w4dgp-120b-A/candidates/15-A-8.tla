---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A process in the PRE state has received the broadcaster's INIT message (it may
\* broadcast ECHO); a process in the NOPRE state never broadcasts.  Correct processes
\* only accept a value once they have gathered enough ECHO messages from distinct
\* senders, tolerating up to T Byzantine senders.  The model explores both the case
\* where some correct process received INIT and the case where none did.

VARIABLES correct, faulty, pc, inbox, sentMsgs

vars == <<correct, faulty, pc, inbox, sentMsgs>>

\* All messages that any correct process has ever sent.  A Byzantine process may
\* inject any ECHO(sender) message into a process's inbox, so the inbox need not be
\* a subset of sentMsgs.

RECURSIVE Receivers(_)
Receivers(S) ==
  IF S = {} THEN {}
  ELSE LET p == CHOOSE x \in S : TRUE
       IN UNION {sender : sender \in {q \in {1..N} : [id |-> p, ty |-> "ECHO"] \in sentMsgs}}
                UNION Receivers(S \ {p})

InitRecs == {p \in correct : pc[p] = "pre"}

MessTypes == {"ECHO"}
Msgs == {p \in {1..N}, t \in MessTypes : [id |-> p, ty |-> t]}

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> {"pre", "nopre", "echoed", "accepted"}]
  /\ inbox \in [1..N -> SUBSET Msgs]
  /\ sentMsgs \subseteq Msgs

Init ==
  /\ Cardinality(correct) = N - F
  /\ correct \cup faulty = 1..N
  /\ correct \cap faulty = {}
  /\ \E S \in {[p \in 1..N -> {"pre", "nopre"}] : \A p \in 1..N : pc[p] = S[p]}
  /\ inbox = [p \in 1..N |-> {}]
  /\ sentMsgs = {}

InitNoBcast ==
  /\ Cardinality(correct) = N - F
  /\ \A p \in 1..N : pc[p] = IF p \in correct THEN "nopre" ELSE "pre"
  /\ inbox = [p \in 1..N |-> {}]
  /\ sentMsgs = {}

Bcast(p, q) == sentMsgs' = sentMsgs \cup {[id |-> q, ty |-> "ECHO"]} /\ UNCHANGED <<correct, faulty, pc, inbox>>

Recv(p, m) == inbox' = [inbox EXCEPT ![p] = inbox[p] \cup {m}] /\ UNCHANGED <<correct, faulty, pc, sentMsgs>>

Deliver(p) == Bcast(p, p) /\ pc' = [pc EXCEPT ![p] = "echoed"]

\* A correct process that has not yet broadcast may collect messages from any sender,
\* including a Byzantine one; it only needs N-2T distinct correct senders to broadcast,
\* and N-T distinct correct senders to broadcast and accept immediately.
Collect(p) ==
  /\ pc[p] \in {"pre", "nopre"}
  /\ Cardinality({q \in correct : [id |-> q, ty |-> "ECHO"] \in inbox[p]}) >= N - 2 * T
  /\ Cardinality({q \in correct : [id |-> q, ty |-> "ECHO"] \in inbox[p]}) < N - T
  /\ Deliver(p) /\ UNCHANGED <<correct, faulty, inbox>>

CollectThenAccept(p) ==
  /\ pc[p] \in {"pre", "nopre"}
  /\ Cardinality({q \in correct : [id |-> q, ty |-> "ECHO"] \in inbox[p]}) >= N - T
  /\ Deliver(p) /\ pc' = [pc EXCEPT ![p] = "accepted"] /\ UNCHANGED <<correct, faulty, inbox>>

Accept(p) ==
  /\ pc[p] = "echoed"
  /\ Cardinality({q \in correct : [id |-> q, ty |-> "ECHO"] \in inbox[p]}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, inbox, sentMsgs>>

DoBcast(p) == Deliver(p) \/ Collect(p) \/ CollectThenAccept(p) \/ Accept(p)

RecvSome(p) == \E m \in {Msgs, [id |-> p, ty |-> "ECHO"]} : Recv(p, m)

ReceiveAll == \E p \in correct : RecvSome(p) \/ DoBcast(p)

Next == ReceiveAll \/ Init \/ InitNoBcast

Spec == Init /\ [][Next]_vars

NoBcastSpec == InitNoBcast /\ [][Next]_vars

\* With no correct broadcaster, no correct process ever accepts (the message is
\* unforgeable).  With a broadcaster, every correct process eventually accepts.
UnforgLtl == NoBcastSpec => (InitRecs = {} => \A p \in correct : <>(pc[p] = "accepted"))
CorrLtl == InitRecs = correct => \A p \in correct : <>(pc[p] = "accepted")
RelayLtl == (\E p \in correct : pc[p] = "accepted") => \A p \in correct : <>(pc[p] = "accepted")

\* Strong fairness per correct process on the ability to receive and act (once the
\* network has settled, a correct process that can keep receiving messages and acting
\* must do so), and weak fairness where that ability is blocked.
FAIRNESS ==
  /\ \A p \in correct : WF_vars(DoBcast(p))
  /\ \A p \in correct : SF_vars(RecvSome(p))

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

====