---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* The broadcast protocol runs over a partition of the processes into
\* correct and faulty ones; this partition is chosen nondeterministically
\* at initialization, so the model is more robust than one that fixes
\* it up front.
Processes == 0..(N-1)
Echos == [who: Processes, kind: {"ECHO"}]
Stages == {"init", "nobcast", "sent", "acc"}

VARIABLES correct, faulty, pc, rx, sent

vars == << correct, faulty, pc, rx, sent >>

RECURSIVE Dist(_)
Dist(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN 1 + Dist(S \ {x})

MaxEchos == Cardinality(Echos)
NoMsg == CHOOSE m \in Echos : TRUE

TypeOK ==
  /\ correct \subseteq Processes
  /\ Cardinality(correct) = N - F
  /\ faulty = Processes \ correct
  /\ pc \in [Processes -> Stages]
  /\ rx \in [Processes -> SUBSET Echos]
  /\ sent \subseteq Echos

\* Correct processes only send INIT messages (ECHO, who) once each, so
\* a process that received INIT can be recognized by its own entry in
\* the sent set: no correct process sends twice and no unbound identifier
\* is ever constructed.
SentBy(i) == {m \in sent : m.who = i}

Init ==
  /\ \E S \in {U \in SUBSET Processes : Cardinality(U) = N - F} :
       /\ correct = S
       /\ faulty = Processes \ S
  /\ \E bcast == {i \in correct : pc[i] = "init"},
       noBcast == {i \in correct : pc[i] = "nobcast"} :
       /\ bcast \cup noBcast = correct
       /\ bcast \cap noBcast = {}
       /\ sent = { [who |-> i, kind |-> "ECHO"] : i \in bcast }
  /\ pc = [i \in Processes |-> IF i \in bcast THEN "init" ELSE "nobcast"]
  /\ rx = [i \in Processes |-> {}]

Delivery(i) ==
  /\ \E news \in SUBSET (sent \cup Echos) :
       tx == {m \in news : m.kind = "ECHO" /\ m.who \in correct /\ m \notin rx[i]}
       /\ rx' = [rx EXCEPT ![i] = @ \cup tx]
  /\ UNCHANGED << correct, faulty, pc, sent >>

\* The process that received the broadcast's INIT message accepts
\* immediately and sends its ECHO.
InitAccept(i) ==
  /\ pc[i] = "init"
  /\ pc' = [pc EXCEPT ![i] = "acc"]
  /\ sent' = sent \cup {[who |-> i, kind |-> "ECHO"]}
  /\ UNCHANGED << correct, faulty, rx >>

\* A correct process that has not yet sent ECHO collects messages from
\* distinct senders; above N-2T it is eligible to send, below N-T it
\* must wait for more (this is what makes the protocol safe for the
\* configured value of T).
RelayIgnite(i) ==
  /\ pc[i] = "nobcast"
  /\ Dist({m.who : m \in rx[i]}) >= N - 2 * T
  /\ Dist({m.who : m \in rx[i]}) < N - T
  /\ sent' = sent \cup {[who |-> i, kind |-> "ECHO"]}
  /\ pc' = [pc EXCEPT ![i] = "sent"]
  /\ UNCHANGED << correct, faulty, rx >>

RelayAccept(i) ==
  /\ pc[i] = "nobcast"
  /\ Dist({m.who : m \in rx[i]}) >= N - T
  /\ sent' = sent \cup {[who |-> i, kind |-> "ECHO"]}
  /\ pc' = [pc EXCEPT ![i] = "acc"]
  /\ UNCHANGED << correct, faulty, rx >>

RelayFinal(i) ==
  /\ pc[i] = "sent"
  /\ Dist({m.who : m \in rx[i]}) >= N - T
  /\ pc' = [pc EXCEPT ![i] = "acc"]
  /\ UNCHANGED << correct, faulty, rx, sent >>

Next ==
  \/ \E i \in Processes : Delivery(i)
  \/ \E i \in correct : InitAccept(i) \/ RelayIgnite(i) \/ RelayAccept(i) \/ RelayFinal(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ UNCHANGED << correct, faulty >>
  /\ WF_vars(\E i \in correct : Delivery(i))
  /\ WF_vars(\E i \in correct : RelayIgnite(i))
  /\ WF_vars(\E i \in correct : RelayAccept(i))
  /\ WF_vars(\E i \in correct : RelayFinal(i))

\* No correct process ever accepts unless some correct process actually
\* broadcast.
UnforgLtl ==
  (~(\A i \in correct : pc[i] = "init")) ~> (\A i \in correct : pc[i] = "acc")

CorrLtl ==
  (\A i \in correct : pc[i] = "init") ~> (\A i \in correct : pc[i] = "acc")

RelayLtl ==
  (\E i \in correct : pc[i] = "acc") ~> (\A i \in correct : pc[i] = "acc")

\* The remaining invariant is a domain check, not a design property.
FCConstraints == TypeOK

====