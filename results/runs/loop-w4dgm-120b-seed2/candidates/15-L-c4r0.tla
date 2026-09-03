---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* The action set is kept intentionally small: a process only ever receives
\* messages that correct processes have actually sent, plus any arbitrary
\* messages from the small set of Byzantine processes.
Messages == {"ech"}

VARIABLES pcs, recv, sentMsgs, correct, faulty

vars == <<pcs, recv, sentMsgs, correct, faulty>>

\* pcs tracks the control location ("phase") of each process; pcs[p] is
\* "init" iff p was seeded with the broadcaster's message, and "echo" means
\* p has already sent its own ECHO message.  recv[p] is the set of distinct
\* sender identities whose messages p has observed so far.
TypeOK ==
  /\ pcs \in [1..N -> {"init", "none", "echo", "accept"}]
  /\ recv \in [1..N -> SUBSET (1..N)]
  /\ sentMsgs \subseteq (1..N) \X Messages
  /\ correct \subseteq 1..N
  /\ faulty = (1..N) \ correct

Init ==
  /\ pcs \in {[init |-> "init", none |-> "none"]} [ 1..N -> {"init", "none"} ]
  /\ recv = [p \in 1..N |-> {}]
  /\ sentMsgs = {}
  /\ \E C \in SUBSET 1..N : Cardinality(C) = N - F /\ correct = C
  /\ faulty = (1..N) \ correct

NoInit ==
  /\ \A p \in correct : pcs[p] = "none"
  /\ sentMsgs = {}

\* Fairness Stays With the Receivers: a correct process that can always
\* still receive messages is given a weakly fair chance to do so.
ReceiveMsg(p, m) ==
  /\ p \in correct
  /\ m \notin recv[p]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<pcs, sentMsgs, correct, faulty>>

SendEcho(p) ==
  /\ p \in correct
  /\ pcs[p] \in {"init", "none"}
  /\ sentMsgs' = sentMsgs \cup {<<p, "ech">>}
  /\ pcs' = [pcs EXCEPT ![p] = "echo"]
  /\ UNCHANGED <<recv, correct, faulty>>

Accept(p) ==
  /\ p \in correct
  /\ pcs[p] # "accept"
  /\ \E s \in [Messages -> SUBSET 1..N] :
       \A m \in Messages : s[m] = { q \in 1..N : <<q, m>> \in sentMsgs }
  /\ (Cardinality(s["ech"] \cap correct) >= N - T
  /\ pcs' = [pcs EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<recv, sentMsgs, correct, faulty>>

\* A Byzantine process may send any subset of message types it likes.
SendByz(p) ==
  /\ p \in faulty
  /\ sentMsgs' = sentMsgs \cup { <<p, m>> : m \in Messages }
  /\ UNCHANGED <<pcs, recv, correct, faulty>>

ReceiveStep ==
  \E p \in 1..N, m \in Messages : ReceiveMsg(p, m)

Next ==
  \/ ReceiveStep
  \/ \E p \in 1..N : SendEcho(p) \/ Accept(p) \/ SendByz(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ReceiveStep)
  /\ \A p \in 1..N : SF_vars(SendEcho(p))
  /\ \A p \in 1..N : SF_vars(Accept(p))

\* SAFETY: unforgeability of the broadcast is a property of the reachable
\* states alone, independent of the fairness assumptions on ReceiveStep.
UnforgLtl ==
  (NoInit) => (\A p \in correct : pcs[p] # "accept")

CorrLtl == (\A p \in 1..N : pcs[p] = "init") ~> (\A p \in correct : pcs[p] = "accept")
RelayLtl == (\E p \in correct : pcs[p] = "accept") ~> (\A p \in correct : pcs[p] = "accept")

\* FCConstraints is the type-checking invariant from the spec; it is a
\* separate fact from unforgeability and is needed for the full model check.
FCConstraints == TypeOK

====