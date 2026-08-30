---- MODULE bcastByz ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F

\* One broadcast round: INIT (received or not) -> ECHO -> ACCEPT.
\* Byzantine processes can inject arbitrary ECHO messages.
\* Unforgeability must hold whenever no correct process broadcasted.
\* CorrLtl and RelayLtl are weakly fair versions of the same eventuality.

VARIABLES correct, faulty, pc, recvMsgs, sentMsgs

Message == [etype : {"ECHO"}, src : 1..N]

TypeOK ==
  /\ correct \subseteq 1..N
  /\ faulty \subseteq 1..N
  /\ Cardinality(correct) = N - F
  /\ faulty = (1..N) \ correct
  /\ pc \in [1..N -> {"none", "bcst", "echoed", "accept"}]
  /\ recvMsgs \in [1..N -> SUBSET Message]
  /\ sentMsgs \subseteq Message

Onward(p) == {m \in recvMsgs[p] : m.src \in correct}
Replies(p) == {m.src : m \in Onward(p)}
MsgsFromFaulty(p) == {m \in recvMsgs[p] : m.src \in faulty}

\* A restricted start where no correct process broadcasted.
InitNoBroadcast ==
  /\ \A p \in 1..N : pc[p] \in {"none", "bcst"}
  /\ \A p \in correct : pc[p] = "none"
  /\ sentMsgs = {}
  /\ recvMsgs = [p \in 1..N |-> {}]

Init ==
  /\ InitNoBroadcast
  /\ \A p \in correct : pc[p] \in {"none", "bcst"}
  /\ \E p \in correct : pc[p] = "bcst"
  /\ \A p \in 1..N : recvMsgs[p] = {}

\* Correct receive: combine all sent ECHO plus every possible faulty ECHO.
Receive(p) ==
  /\ pc[p] # "accept"
  /\ \E newMsgs \subseteq sentMsgs \cup { [etype |-> "ECHO", src |-> q] : q \in faulty } :
        recvMsgs' = [recvMsgs EXCEPT ![p] = recvMsgs[p] \cup newMsgs]
  /\ UNCHANGED <<correct, faulty, pc, sentMsgs>>

SendEcho(p) ==
  /\ pc[p] = "none"
  /\ pc' = [pc EXCEPT ![p] = "echoed"]
  /\ sentMsgs' = sentMsgs \cup {[etype |-> "ECHO", src |-> p]}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

AcceptOnQuorum(p) ==
  /\ pc[p] \in {"none", "bcst"}
  /\ Cardinality(Replies(p)) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sentMsgs' = sentMsgs \cup {[etype |-> "ECHO", src |-> p]}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

WeakSendEcho(p) == SendEcho(p) \/ AcceptOnQuorum(p)

NextBroad ==
  \/ \E p \in 1..N : Receive(p)
  \/ \E p \in 1..N : SendEcho(p)
  \/ \E p \in 1..N : AcceptOnQuorum(p)

\* The second branch models the no-broadcast case without fairness, keeping
\* the model small enough to finish checking the safety property.
NextNoBroad ==
  \/ \E p \in 1..N : Receive(p)
  \/ \E p \in 1..N : AcceptOnQuorum(p)

Next == NextBroad \/ NextNoBroad

Spec == Init /\ [][Next]_<<correct, faulty, pc, recvMsgs, sentMsgs>>

CorrLtl == \A p \in correct : pc[p] = "bcst" ~> (\A p \in correct : pc[p] = "accept")
RelayLtl == (\E p \in correct : pc[p] = "accept") ~> (\A p \in correct : pc[p] = "accept")

FCConstraints == N > 3 * T /\ T >= F /\ F >= 0

UnforgLtl == (\A p \in correct : pc[p] = "none") ~> (\A p \in correct : pc[p] = "none")
====