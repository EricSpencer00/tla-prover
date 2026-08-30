---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A process can be in: broadcast-received, not-yet-received, sent-ECHO, or accepted.
Locs == {"bcast", "none", "echoed", "accepted"}

VARIABLES correct, faulty, loc, rcvd, sent
vars == <<correct, faulty, loc, rcvd, sent>>

\* A message is a sender identity together with the ECHO label.
Msg == N * ("echo")
Pairs == (1..N) \X {"echo"}
Echos(k) == {m["snd"] : m \in {y \in rcvd[k] : y["type"] = "echo"}}

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ loc \in [1..N -> Locs]
  /\ rcvd \in [1..N -> SUBSET Pairs]
  /\ sent \subseteq Pairs

Init ==
  /\ correct = 1..(N - F)
  /\ faulty = (1..N) \ correct
  /\ loc = [k \in 1..N |-> IF k \in correct THEN "bcast" ELSE "none"]
  /\ rcvd = [k \in 1..N |-> {}]
  /\ sent = {}

\* The senders k may be either correct or Byzantine; the latter are the attacker.
SendMsg(k, mtype) == [snd |-> k, type |-> mtype]
Alt(m) == SendMsg(IF m["snd"] \in correct THEN 2 ELSE 1, m["type"])

\* A correct process may receive any set that extends its current view, but never more.
Receive(k, S) ==
  /\ k \in correct
  /\ S \subseteq (sent \cup {Alt(m) : m \in sent})
  /\ S # {}
  /\ rcvd' = [rcvd EXCEPT ![k] = @ \cup S]
  /\ UNCHANGED <<correct, faulty, loc, sent>>

\* Someone that got the INIT message accepts and relays immediately.
RelayInit(k) ==
  /\ k \in correct
  /\ loc[k] = "bcast"
  /\ loc' = [loc EXCEPT ![k] = "accepted"]
  /\ sent' = sent \cup {SendMsg(k, "echo")}
  /\ UNCHANGED <<correct, faulty, rcvd>>

\* With enough ECHOs but not yet a quorum, it relays but delays acceptance.
RelayGather(k) ==
  /\ k \in correct
  /\ loc[k] = "none"
  /\ Cardinality(Echos(k)) >= N - 2 * T
  /\ Cardinality(Echos(k)) < N - T
  /\ loc' = [loc EXCEPT ![k] = "echoed"]
  /\ sent' = sent \cup {SendMsg(k, "echo")}
  /\ UNCHANGED <<correct, faulty, rcvd>>

RelayAccept(k) ==
  /\ k \in correct
  /\ loc[k] \in {"none", "echoed"}
  /\ Cardinality(Echos(k)) >= N - T
  /\ loc' = [loc EXCEPT ![k] = "accepted"]
  /\ sent' = sent \cup {SendMsg(k, "echo")}
  /\ UNCHANGED <<correct, faulty, rcvd>>

RelayBehind(k) ==
  /\ k \in correct
  /\ loc[k] = "echoed"
  /\ Cardinality(Echos(k)) >= N - T
  /\ loc' = [loc EXCEPT ![k] = "accepted"]
  /\ UNCHANGED <<correct, faulty, rcvd, sent>>

Next ==
  \/ \E k \in 1..N, S \in SUBSET Pairs: Receive(k, S)
  \/ \E k \in correct: RelayInit(k) \/ RelayGather(k) \/ RelayAccept(k) \/ RelayBehind(k)

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(\E k \in correct, S \in SUBSET Pairs: Receive(k, S))
  /\ WF_vars(\E k \in correct: RelayGather(k) \/ RelayAccept(k))

CorrLtl == <>(\A k \in correct: loc[k] = "accepted")
RelayLtl == (\E k \in correct: loc[k] = "accepted") ~> (\A k \in correct: loc[k] = "accepted")
UnforgLtl == (\A k \in correct: loc[k] # "bcast") ~> (\A k \in correct: loc[k] # "accepted")

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
====