---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

Correct == "correct"
Faulty == "faulty"
ECHO == "ECHO"
INIT == "INIT"
Loc == {ECHO, INIT, "none"}

VARIABLES procType, loc, recv, sent, accepted

Vars == <<procType, loc, recv, sent, accepted>>

TypeOK ==
  /\ procType \in [1..N -> {Correct, Faulty}]
  /\ loc \in [1..N -> Loc]
  /\ recv \in [1..N -> SUBSET (1..N \X Loc)]
  /\ sent \subseteq (1..N \X Loc)
  /\ accepted \subseteq 1..N

FCConstraints ==
  /\ Cardinality(accepted) <= N
  /\ Cardinality(sent) <= N
  /\ Cardinality({i \in 1..N : procType[i] = Correct}) = N - F
  /\ Cardinality({i \in 1..N : procType[i] = Faulty}) = F
  /\ \A i \in 1..N : loc[i] \in Loc
  /\ \A i \in 1..N : \A m \in recv[i] : m[2] \in Loc

Init ==
  /\ procType = [i \in 1..N |-> IF i <= N - F THEN Correct ELSE Faulty]
  /\ loc = [i \in 1..N |-> IF i = 1 THEN INIT ELSE "none"]
  /\ recv = [i \in 1..N |-> {}]
  /\ sent = {}
  /\ accepted = {}

\* Correct processes only ever receive messages sent by correct processes plus
\* an arbitrary (adversarial) set of messages from Byzantine processes.
Receive(i) ==
  /\ procType[i] = Correct
  /\ \E m \in SUBSET (sent \cup (1..N \X {ECHO})) :
       recv' = [recv EXCEPT ![i] = recv[i] \cup m]
  /\ UNCHANGED <<procType, loc, sent, accepted>>

SendEcho(i) ==
  /\ procType[i] = Correct
  /\ loc' = [loc EXCEPT ![i] = ECHO]
  /\ sent' = sent \cup {<<i, ECHO>>}
  /\ UNCHANGED <<procType, recv, accepted>>

\* A correct process with no INIT may still act once it has collected enough
\* echo messages from distinct senders.
ActEcho(i) ==
  /\ procType[i] = Correct
  /\ loc[i] = "none"
  /\ Cardinality({m \in recv[i] : m[2] = ECHO}) >= N - 2T
  /\ Cardinality({m \in recv[i] : m[2] = ECHO}) < N - T
  /\ sent' = sent \cup {<<i, ECHO>>}
  /\ UNCHANGED <<procType, loc, recv, accepted>>

AcceptEarly(i) ==
  /\ procType[i] = Correct
  /\ loc[i] = "none"
  /\ Cardinality({m \in recv[i] : m[2] = ECHO}) >= N - T
  /\ loc' = [loc EXCEPT ![i] = ECHO]
  /\ sent' = sent \cup {<<i, ECHO>>}
  /\ UNCHANGED <<procType, recv, accepted>>

\* After an ECHO has already been sent, a correct process may accept once it
\* has collected the full threshold of echo messages from distinct senders.
AcceptLate(i) ==
  /\ procType[i] = Correct
  /\ loc[i] = ECHO
  /\ i \notin accepted
  /\ Cardinality({m \in recv[i] : m[2] = ECHO}) >= N - T
  /\ accepted' = accepted \cup {i}
  /\ UNCHANGED <<procType, loc, recv, sent>>

Next ==
  \/ \E i \in 1..N : Receive(i)
  \/ \E i \in 1..N : SendEcho(i)
  \/ \E i \in 1..N : ActEcho(i)
  \/ \E i \in 1..N : AcceptEarly(i)
  \/ \E i \in 1..N : AcceptLate(i)

Spec ==
  /\ Init /\ [][Next]_Vars
  /\ WF_Vars(\E i \in 1..N : Receive(i))
  /\ WF_Vars(\E i \in 1..N : ActEcho(i))

\* Broadcast with no sender: no correct process should ever be able to accept.
UnforgLtl == (\A i \in 1..N : procType[i] = Faulty) ~> (\A i \in 1..N : procType[i] = Correct => i \notin accepted)

CorrLtl == (\A i \in 1..N : loc[i] = INIT) ~> (\A i \in 1..N : procType[i] = Correct => i \in accepted)

RelayLtl == (\E i \in 1..N : i \in accepted) ~> (\A i \in 1..N : procType[i] = Correct => i \in accepted)

====