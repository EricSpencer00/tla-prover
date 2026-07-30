---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME N \in Nat /\ N >= 1 /\ N > 3 * T /\ T \in Nat /\ F \in Nat /\ T >= F

\* message type (the only typed content allowed in the model)
Messages == { "ECHO" }

VARIABLES correct, faulty, control, recv, sent

vars == << correct, faulty, control, recv, sent >>

BcastStates == { "broad", "nobroad" }
Locs == { "init", "sent", "done" }

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ \A a \in 1..N : control[a] \in BcastStates
  /\ \A a \in 1..N : recv[a] \subseteq (1..N) \X Messages
  /\ sent \subseteq (1..N) \X Messages

\* No guarantee by the model alone about who the correct broadcasters are.
FCConstraints ==
  /\ Cardinality(correct) = N - F
  /\ correct \cap faulty = {}
  /\ correct \cup faulty = (1..N)
  /\ \A a \in 1..N : control[a] \in BcastStates

Init ==
  /\ correct = CHOOSE C \subseteq (1..N) : Cardinality(C) = N - F
  /\ faulty = (1..N) \ C
  /\ control = [a \in 1..N |-> IF a \in correct THEN "broad" ELSE "nobroad"]
  /\ recv = [a \in 1..N |-> {}]
  /\ sent = {}

\* A correct participant receives a batch of messages from correct and from the
\* Byzantine set at once (asynchronous, unordered, possibly many at once).
ReceiveMore ==
  /\ \E a \in correct :
       /\ recv' = [recv EXCEPT ![a] = recv[a] \cup
                                   (\E m \in sent \cup (faulty \X Messages) : m)]
       /\ control' = [control EXCEPT ![a] =
                       IF control[a] = "init" /\ control[a] = "broad"
                       THEN "sent" ELSE control[a]]
  /\ UNCHANGED << correct, faulty, sent >>

SendEcho(a) ==
  /\ sent' = sent \cup (a \X Messages)
  /\ control' = [control EXCEPT ![a] = "sent"]

\* A participant that never saw the init starts with a quorum short of decision.
Quorum1(a) ==
  /\ Cardinality({ p \in 1..N : << p, "ECHO" >> \in recv[a] }) >= N - 2 * T
  /\ Cardinality({ p \in 1..N : << p, "ECHO" >> \in recv[a] }) < N - T
  /\ control[a] = "init"
  /\ control[a] # "broad"
  /\ SendEcho(a)
  /\ UNCHANGED << correct, faulty, recv >>

Quorum2(a) ==
  /\ Cardinality({ p \in 1..N : << p, "ECHO" >> \in recv[a] }) >= N - T
  /\ control[a] = "init"
  /\ control[a] # "broad"
  /\ SendEcho(a)
  /\ control' = [control EXCEPT ![a] = "done"]
  /\ UNCHANGED << correct, faulty, recv >>

Quorum3(a) ==
  /\ Cardinality({ p \in 1..N : << p, "ECHO" >> \in recv[a] }) >= N - T
  /\ control[a] = "sent"
  /\ control[a] # "broad"
  /\ control' = [control EXCEPT ![a] = "done"]
  /\ UNCHANGED << correct, faulty, recv, sent >>

Next ==
  \/ ReceiveMore
  \/ \E a \in correct : Quorum1(a)
  \/ \E a \in correct : Quorum2(a)
  \/ \E a \in correct : Quorum3(a)

\* Fairness is only for the progress of correct participants; it is omitted from
\* the safety-only configuration that checks UnforgLtl.
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A a \in correct : WF_vars(Quorum1(a))
  /\ \A a \in correct : WF_vars(Quorum2(a))
  /\ \A a \in correct : WF_vars(Quorum3(a))

\* Safety: no correct participant accepts unless at least one was a broadcaster.
UnforgLtl ==
  ( \A a \in correct : control[a] # "broad" ) ~> ( \A a \in correct : control[a] = "done" )

\* Liveness: if all started as broadcasters, all decide.
CorrLtl ==
  (\A a \in correct : control[a] = "broad") ~> (\A a \in correct : control[a] = "done")

RelayLtl ==
  (\E a \in correct : control[a] = "done") ~> (\A a \in correct : control[a] = "done")

====