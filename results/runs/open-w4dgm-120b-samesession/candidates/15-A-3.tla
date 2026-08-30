---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* States: whether a correct process received the broadcaster's INIT message,
\* whether it has sent an ECHO, and whether it has accepted.
Locs == {"org", "nong", "sent", "accept"}

VARIABLES correct, faulty, ctrl, rcvd, sent

vars == <<correct, faulty, ctrl, rcvd, sent>>

\* The sender set of a received message must stay unique once an accept
\* decision stabilizes, so messages are stored as sender/type pairs.
Msg == {<<"echo", i>> : i \in 1..N}

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ ctrl \in [1..N -> Locs]
  /\ rcvd \in [1..N -> SUBSET Msg]
  /\ sent \subseteq Msg

Init ==
  /\ correct = {1..(N - F)}
  /\ faulty = {1..N} \ faulty
  /\ ctrl = [i \in 1..N |-> IF i \in (correct \cap {1..F}) THEN "org" ELSE "nong"]
  /\ rcvd = [i \in 1..N |-> {}]
  /\ sent = {}

\* Fairness is only assumed on this receive-and-act combined step for correct
\* processes; the no-broadcast case is checked without it.
Receive(i) ==
  /\ i \in correct
  /\ ctrl[i] \in {"org", "nong"}
  /\ rcvd' = [rcvd EXCEPT ![i] = rcvd[i] \cup ({x \in sent : x[1] = "echo"} \cup {<<"echo", j>> : j \in faulty})]
  /\ UNCHANGED <<correct, faulty, ctrl, sent>>

InitEcho(i) ==
  /\ i \in correct
  /\ ctrl[i] = "org"
  /\ ctrl' = [ctrl EXCEPT ![i] = "accept"]
  /\ sent' = sent \cup {<<"echo", i>>}
  /\ UNCHANGED <<correct, faulty, rcvd>>

EchoBefore(i) ==
  /\ i \in correct
  /\ ctrl[i] = "nong"
  /\ Cardinality({x \in rcvd[i] : x[1] = "echo"}) >= N - 2 * T
  /\ Cardinality({x \in rcvd[i] : x[1] = "echo"}) < N - T
  /\ ctrl' = [ctrl EXCEPT ![i] = "sent"]
  /\ sent' = sent \cup {<<"echo", i>>}
  /\ UNCHANGED <<correct, faulty, rcvd>>

EchoAccept(i) ==
  /\ i \in correct
  /\ ctrl[i] = "nong"
  /\ Cardinality({x \in rcvd[i] : x[1] = "echo"}) >= N - T
  /\ ctrl' = [ctrl EXCEPT ![i] = "accept"]
  /\ sent' = sent \cup {<<"echo", i>>}
  /\ UNCHANGED <<correct, faulty, rcvd>>

EchoRelay(i) ==
  /\ i \in correct
  /\ ctrl[i] = "sent"
  /\ Cardinality({x \in rcvd[i] : x[1] = "echo"}) >= N - T
  /\ ctrl' = [ctrl EXCEPT ![i] = "accept"]
  /\ UNCHANGED <<correct, faulty, rcvd, sent>>

Next == \E i \in 1..N : Receive(i) \/ InitEcho(i) \/ EchoBefore(i) \/ EchoAccept(i) \/ EchoRelay(i)

Spec == Init /\ [][Next]_vars

\* If no correct process sends an INIT, no correct process may ever accept.
UnforgLtl == (\A i \in correct : ctrl[i] # "org") ~> (\A i \in correct : ctrl[i] = "accept")

CorrLtl == (\A i \in correct : ctrl[i] = "org") ~> (\A i \in correct : ctrl[i] = "accept")

RelayLtl == (\E i \in correct : ctrl[i] = "accept") ~> (\A i \in correct : ctrl[i] = "accept")

FCConstraints == N > 3 * T /\ T >= F /\ F >= 0

====