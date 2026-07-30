---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, loc, recv, sent
vars == << correct, faulty, loc, recv, sent >>

InitCounts == {"hasINIT", "noINIT"}
Locations == {"hasINIT", "noINIT", "echoed", "accepted"}
MsgKinds == {"ECHO"}

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ Cardinality(correct) = N - F
  /\ faulty = (1..N) \ correct
  /\ loc \in [1..N -> Locations]
  /\ recv \in [1..N -> SUBSET [sender: 1..N, kind: MsgKinds]]
  /\ sent \subseteq (1..N)

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ \A p \in 1..N: loc[p] \in InitCounts

Init ==
  /\ loc \in [1..N -> InitCounts]
  /\ correct \subseteq (1..N)
  /\ Cardinality(correct) = N - F
  /\ faulty = (1..N) \ correct
  /\ recv = [p \in 1..N |-> {}]
  /\ sent = {}

InitNoBroadcast ==
  /\ Init
  /\ \A p \in correct: loc[p] = "noINIT"

CorrectMsgs(p) ==
  {m \in sent : m.sender \in correct}

RecvAndAct(p) ==
  /\ loc[p] \in {"hasINIT", "noINIT"}
  /\ \E S \in SUBSET (CorrectMsgs(p) \cup [sender: 1..N, kind: "ECHO"]):
       /\ recv' = [recv EXCEPT ![p] = recv[p] \cup S]
       /\ IF loc[p] = "hasINIT"
          THEN loc' = [loc EXCEPT ![p] = "accepted"]
          ELSE loc' = [loc EXCEPT ![p] = "echoed"]
       /\ sent' = sent \cup {[sender |-> p, kind |-> "ECHO"]}
  /\ UNCHANGED << correct, faulty >>

Echoes(p) == {m \in recv[p] : m.kind = "ECHO"}
DistinctSenders(p, S) == Cardinality({m \in S : m.kind = "ECHO"}) >= Cardinality(S)

RelayStep(p) ==
  /\ loc[p] = "echoed"
  /\ DistinctSenders(p, recv[p])
  /\ recv[p] \subseteq sent
  /\ Cardinality(Echoes(p)) >= N - T
  /\ loc' = [loc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED << correct, faulty, recv, sent >>

AcceptStep(p) ==
  /\ loc[p] = "echoed"
  /\ DistinctSenders(p, recv[p])
  /\ recv[p] \subseteq sent
  /\ Cardinality(Echoes(p)) >= N - 2 * T
  /\ loc' = [loc EXCEPT ![p] = "echoed"]
  /\ sent' = sent \cup {[sender |-> p, kind |-> "ECHO"]}
  /\ UNCHANGED << correct, faulty, recv >>

NoStep(p) == UNCHANGED vars

Next ==
  \/ \E p \in 1..N: RecvAndAct(p) \/ RelayStep(p) \/ AcceptStep(p)
  \/ \E p \in 1..N: NoStep(p)

Spec == Init /\ [][Next]_vars
Liveness == InitNoBroadcast /\ [][Next]_vars

CorrLtl == (correct # {}) ~> (\A p \in correct: loc[p] = "accepted")
RelayLtl == (\E p \in correct: loc[p] = "accepted") ~> (\A p \in correct: loc[p] = "accepted")
UnforgLtl == (correct # {}) ~> (\A p \in correct: loc[p] # "accepted")

====