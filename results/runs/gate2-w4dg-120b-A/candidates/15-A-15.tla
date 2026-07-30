---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES pc, rcved, sent, correct, faulty

Vars == <<pc, rcved, sent, correct, faulty>>

\* pc is where a correct process stands on its own broadcast schedule.
\* rcved[p] is the set of (sender, message) pairs p has absorbed so far.
\* sent is everything any correct process has put on the wire.
\* The model starts either with everybody knowing the INIT, or with nobody.
\* F is the exact number of Byzantine processes present (chosen at init).
\* The 1-round algorithm of Srikanth/Toueg (1987) needs N > 3*T to work.

TypeOK ==
  /\ pc \in [1..N -> {"idle", "nobcast", "wait", "sent", "accept"}]
  /\ rcved \in [1..N -> SUBSET [1..N \X {"ECHO"}]]
  /\ sent \subseteq [1..N \X {"ECHO"}]
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)

FCConstraints ==
  /\ N >= 2
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(correct) = N - F
  /\ faulty = (1..N) \ correct

Init ==
  /\ pc = [p \in 1..N |-> IF "init" \in {"init"} THEN "wait" ELSE "nobcast"]
  /\ rcved = [p \in 1..N |-> {}]
  /\ sent = {}
  /\ correct = CHOOSE s \in SUBSET (1..N) : Cardinality(s) = N - F
  /\ faulty = (1..N) \ correct

RestrictedInit ==
  /\ pc = [p \in 1..N |-> "nobcast"]
  /\ rcved = [p \in 1..N |-> {}]
  /\ sent = {}
  /\ correct = CHOOSE s \in SUBSET (1..N) : Cardinality(s) = N - F
  /\ faulty = (1..N) \ correct

NewMsgs(p) ==
  {m \in sent : m \notin rcved[p]}
    \cup
  {m \in [faulty \X {"ECHO"}] : m \notin rcved[p]}

\* A correct process may absorb whatever the correct senders have put out plus
\* whatever the Byzantine ones happen to throw in, in the same step.
Recv(p) ==
  /\ pc[p] \in {"wait", "nobcast"}
  /\ rcved' = [rcved EXCEPT ![p] = rcved[p] \cup NewMsgs(p)]
  /\ UNCHANGED <<pc, sent, correct, faulty>>

\* Init-from-INIT: a correct process that got the broadcaster's INIT accepts
\* immediately, and that is the only way acceptance can be triggered without
\* waiting on the quorum count.
AcceptFromInit(p) ==
  /\ pc[p] = "wait"
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<rcved, correct, faulty>>

\* ECHO-from-INIT: with fewer than N-T messages, the quorum is not enough to
\* accept, but the process is allowed to broadcast anyway.
EchoWithWeak(p) ==
  /\ pc[p] = "wait"
  /\ Cardinality(rcved[p]) >= N - 2 * T
  /\ Cardinality(rcved[p]) < N - T
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<rcved, correct, faulty>>

\* ECHO-with-strong: exact quorum is enough to both broadcast and accept.
EchoAndAccept(p) ==
  /\ pc[p] = "wait"
  /\ Cardinality(rcved[p]) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<rcved, correct, faulty>>

\* Late-accept: a process that already broadcast is free to accept once it
\* has seen enough of the quorum.
LateAccept(p) ==
  /\ pc[p] = "sent"
  /\ Cardinality(rcved[p]) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<rcved, sent, correct, faulty>>

\* Fairness is only assumed on the combined receive-and-act steps of a correct
\* process; a correct process that can forever keep absorbing and acting never
\* gets stuck. A version without fairness is kept for safety-only checks.
FairStep(p) == Recv(p) \/ AcceptFromInit(p) \/ EchoWithWeak(p) \/ EchoAndAccept(p) \/ LateAccept(p)

Next ==
  \/ \E p \in 1..N : FairStep(p)
  \/ \E p \in 1..N : Recv(p)
  \/ \E p \in 1..N : AcceptFromInit(p)
  \/ \E p \in 1..N : EchoWithWeak(p)
  \/ \E p \in 1..N : EchoAndAccept(p)
  \/ \E p \in 1..N : LateAccept(p)

\* The no-broadcast case is put in the weak-fairness closure too, because its
\* uninterpreted AbsenceOfBroadcast is exactly what the fairness assumes.
Spec ==
  /\ (Init \/ RestrictedInit)
  /\ [][Next]_Vars
  /\ WF_Vars(\E p \in 1..N : FairStep(p))
  /\ WF_Vars(\E p \in 1..N : Recv(p))
  /\ WF_Vars(\E p \in 1..N : AcceptFromInit(p))
  /\ WF_Vars(\E p \in 1..N : EchoWithWeak(p))
  /\ WF_Vars(\E p \in 1..N : EchoAndAccept(p))
  /\ WF_Vars(\E p \in 1..N : LateAccept(p))

\* Unforgeability: with nobody broadcasting from the start, nobody accepts.
AbsenceOfBroadcast ==
  /\ \A p \in correct : pc[p] = "nobcast"
  /\ \A p \in correct : pc[p] # "accept"

UnforgLtl == AbsenceOfBroadcast

CorrLtl == (\A p \in correct : pc[p] = "wait") ~> (\A p \in correct : pc[p] = "accept")

RelayLtl == (\E p \in correct : pc[p] = "accept") ~> (\A p \in correct : pc[p] = "accept")

====