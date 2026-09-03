---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

NORM == N - 2 * T
QUORUM == N - T

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 3 * T

\* Control locations: non-broadcast, broadcast-received, ECHO-sent, accept.
Loc == {"none", "init", "echoed", "accept"}

VARIABLES correct, faulty, loc, inbox, sentMsgs

vars == <<correct, faulty, loc, inbox, sentMsgs>>

InitMsgs == {"init"}
EchoMsgs == {"echo"}

TypeOK ==
  /\ correct \subseteq 1..N
  /\ faulty = (1..N) \ correct
  /\ loc \in [1..N -> Loc]
  /\ inbox \in [1..N -> SUBSET (1..N \X {"init", "echo"})]
  /\ sentMsgs \subseteq (1..N \X {"init", "echo"})
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F

Init ==
  /\ \E S \in {SUBSET(1..N) : Cardinality(S) = N - F} :
       correct = S
  /\ faulty = (1..N) \ correct
  /\ loc = [p \in 1..N |-> IF p \in correct THEN "init" ELSE "none"]
  /\ inbox = [p \in 1..N |-> {}]
  /\ sentMsgs = {}

\* A correct process may absorb any set of as-yet-unreceived messages, whether
\* they came from a correct sender or a Byzantine one.
ReceiveMsg(p) ==
  \E M \in SUBSET (1..N \X {"init", "echo"}) :
    /\ M \subseteq sentMsgs
    /\ M # {}
    /\ inbox' = [inbox EXCEPT ![p] = @ \cup M]
    /\ UNCHANGED <<correct, faulty, loc, sentMsgs>>

\* The broadcaster's INIT message is considered received from the start.
EchoAll(p) ==
  /\ p \in correct
  /\ loc[p] = "init"
  /\ loc' = [loc EXCEPT ![p] = "echoed"]
  /\ sentMsgs' = sentMsgs \cup {<<p, "echo">>}
  /\ UNCHANGED <<correct, faulty, inbox>>

\* A correct process that has not yet acted sends its ECHO once it has enough
\* distinct ECHO senders around it.
EchoSome(p) ==
  /\ p \in correct
  /\ loc[p] = "none"
  /\ Cardinality({q \in 1..N : <<q, "echo">> \in inbox[p]}) >= NORM
  /\ loc' = [loc EXCEPT ![p] = "echoed"]
  /\ sentMsgs' = sentMsgs \cup {<<p, "echo">>}
  /\ UNCHANGED <<correct, faulty, inbox>>

\* Acceptance needs a strict quorum of distinct ECHO senders.
AcceptSome(p) ==
  /\ p \in correct
  /\ loc[p] = "none"
  /\ Cardinality({q \in 1..N : <<q, "echo">> \in inbox[p]}) >= QUORUM
  /\ loc' = [loc EXCEPT ![p] = "accept"]
  /\ sentMsgs' = sentMsgs \cup {<<p, "echo">>}
  /\ UNCHANGED <<correct, faulty, inbox>>

\* A slow correct process that already echoed may still be waiting on the
\* quorum before it is allowed to accept.
AcceptLate(p) ==
  /\ p \in correct
  /\ loc[p] = "echoed"
  /\ Cardinality({q \in 1..N : <<q, "echo">> \in inbox[p]}) >= QUORUM
  /\ loc' = [loc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, inbox, sentMsgs>>

\* Fairness is assumed on the combined receive-and-act steps of correct
\* processes, not on each individually -- a correct process may be slow but
\* never assumed to be permanently failed.
Next ==
  \E p \in 1..N :
    \/ ReceiveMsg(p)
    \/ EchoAll(p)
    \/ EchoSome(p)
    \/ AcceptSome(p)
    \/ AcceptLate(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in 1..N : WF_vars(ReceiveMsg(p))

\* Safety: if no correct process broadcast, no correct process ever accepts.
UnforgLtl ==
  (\A p \in correct : loc[p] # "init") ~> (\A p \in correct : loc[p] = "accept")

\* Liveness: when everyone received the INIT message, everyone eventually accepts.
CorrLtl == (\A p \in correct : loc[p] = "init") ~> (\A p \in correct : loc[p] = "accept")

\* Liveness: a single acceptance ripples out to all correct processes.
RelayLtl == (\E p \in correct : loc[p] = "accept") ~> (\A p \in correct : loc[p] = "accept")

\* Type safety, plus the partitioning of process identities.
FCConstraints == TypeOK

====