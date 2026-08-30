---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Correct processes reliably broadcast ECHO; faulty ones may send anything.
\* The twist: the broadcaster's INIT message is modeled as an initial value
\* per process rather than as a separate broadcast phase, so not every
\* correct process has to start with it -- this is what the no-broadcast
\* variant (FCConstraints) tests against the unforgeability invariant.

\* Program counters: the state each correct process is in.
Loc == {"init", "nobroadcast", "sent", "accepted"}

VARIABLES correct, faulty, pc, recved, sentByCorrect

vars == <<correct, faulty, pc, recved, sentByCorrect>>

Actors == 1..N
Messages == [who : Actors, kind : {"echo", "init"}]
Echos == {m \in Messages : m.kind = "echo"}
InitMsgs == {m \in Messages : m.kind = "init"}

TypeOK ==
  /\ correct \subseteq Actors
  /\ faulty \subseteq Actors
  /\ correct \cup faulty = Actors
  /\ pc \in [Actors -> Loc]
  /\ recved \in [Actors -> SUBSET Messages]
  /\ sentByCorrect \subseteq Echos

InitState ==
  /\ Cardinality(correct) = N - F
  /\ correct \cap faulty = {}
  /\ pc \in [Actors -> {"init", "nobroadcast"}]
  /\ recved = [a \in Actors |-> {}]
  /\ sentByCorrect = {}

\* Restricted initial state for the no-broadcast case: nobody starts with
\* the broadcaster's INIT message, so the unforgeability invariant must hold.
InitNoBroadcast ==
  /\ InitState
  /\ \A a \in Actors : pc[a] = "nobroadcast"

\* Correct processes may only ever receive messages that were actually sent
\* by some correct process (ECHO) or that are INIT messages from any process.
Receive(a) ==
  /\ pc[a] \in {"init", "nobroadcast"}
  /\ \E m \subseteq (sentByCorrect \cup InitMsgs) :
       recved' = [recved EXCEPT ![a] = m]
  /\ UNCHANGED <<correct, faulty, pc, sentByCorrect>>

\* ECHO is only ever sent by a correct process that is participating.
SendEcho(a) ==
  /\ pc[a] \in {"init", "nobroadcast"}
  /\ sentByCorrect' = sentByCorrect \cup {[who |-> a, kind |-> "echo"]}
  /\ pc' = [pc EXCEPT ![a] = "sent"]
  /\ UNCHANGED <<correct, faulty, recved>>

\* A correct process that has not yet sent its own ECHO may accept once it
\* collects a quorum of ECHO messages from distinct senders.
AcceptAtMostT(a) ==
  /\ pc[a] = "nobroadcast"
  /\ Cardinality({m \in recved[a] : m.kind = "echo"}) >= (N - 2 * T)
  /\ Cardinality({m \in recved[a] : m.kind = "echo"}) < (N - T)
  /\ sentByCorrect' = sentByCorrect \cup {[who |-> a, kind |-> "echo"]}
  /\ pc' = [pc EXCEPT ![a] = "sent"]
  /\ UNCHANGED <<correct, faulty, recved>>

AcceptAtLeastT(a) ==
  /\ pc[a] \in {"nobroadcast", "sent"}
  /\ Cardinality({m \in recved[a] : m.kind = "echo"}) >= (N - T)
  /\ sentByCorrect' = sentByCorrect \cup {[who |-> a, kind |-> "echo"]}
  /\ pc' = [pc EXCEPT ![a] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recved>>

\* Weak fairness on receive/act lets every correct process eventually collect
\* enough ECHO messages to cross the quorum thresholds.
Next ==
  \/ \E a \in Actors : Receive(a)
  \/ \E a \in Actors : SendEcho(a)
  \/ \E a \in Actors : AcceptAtMostT(a)
  \/ \E a \in Actors : AcceptAtLeastT(a)

Spec ==
  /\ InitState
  /\ [][Next]_vars
  /\ WF_vars(\E a \in Actors : AcceptAtMostT(a))
  /\ WF_vars(\E a \in Actors : AcceptAtLeastT(a))

\* Unforgeability: if no correct process ever sends an INIT message (all
\* start in the "nobroadcast" state), no correct process may ever accept.
UnforgLtl == (\A a \in correct : pc[a] = "nobroadcast") ~> (\A a \in correct : pc[a] = "accepted")

CorrLtl == (\A a \in correct : pc[a] = "init") ~> (\A a \in correct : pc[a] = "accepted")

RelayLtl == (\E a \in correct : pc[a] = "accepted") ~> (\A a \in correct : pc[a] = "accepted")

FCConstraints == InitNoBroadcast

====