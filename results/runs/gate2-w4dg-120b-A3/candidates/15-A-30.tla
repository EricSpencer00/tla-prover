---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

VARIABLES corr, faulty, pc, seen, sent

vars == <<corr, faulty, pc, seen, sent>>

Init0 ==
  /\ \E cset \in SUBSET (1..N) :
       /\ Cardinality(cset) = N - F
       /\ corr = cset
       /\ faulty = (1..N) \ cset
  /\ \E pc0 \in [1..N -> {"broadcast", "nobroadcast", "echoed", "accepted"}] :
       pc = pc0
  /\ seen = [i \in 1..N |-> {}]
  /\ sent = {}

InitAll ==
  /\ Init0
  /\ \A i \in 1..N : pc[i] \in {"broadcast", "echoed", "accepted"}

OthersSeen(i) ==
  { j \in 1..N : j # i /\ \E t \in seen[j] : t[2] = "ECHO" }

Receive(i) ==
  /\ i \in corr
  /\ pc[i] \in {"broadcast", "nobroadcast"}
  /\ \E newMsgs \in SUBSET (sent \cup [1..N \times {"ECHO"}]) :
       seen' = [seen EXCEPT ![i] = seen[i] \cup newMsgs]
  /\ UNCHANGED <<corr, faulty, pc, sent>>

SendEcho(i) ==
  /\ i \in corr
  /\ pc[i] \in {"broadcast", "nobroadcast"}
  /\ pc' = [pc EXCEPT ![i] = "echoed"]
  /\ sent' = sent \cup {<<i, "ECHO">>}
  /\ UNCHANGED <<corr, faulty, seen>>

EchoBeforeAccept(i) ==
  /\ i \in corr
  /\ pc[i] \in {"nobroadcast"}
  /\ Cardinality(OthersSeen(i)) >= (N - 2 * T)
  /\ Cardinality(OthersSeen(i)) < (N - T)
  /\ pc' = [pc EXCEPT ![i] = "echoed"]
  /\ sent' = sent \cup {<<i, "ECHO">>}
  /\ UNCHANGED <<corr, faulty, seen>>

EchoAndAccept(i) ==
  /\ i \in corr
  /\ pc[i] \in {"nobroadcast"}
  /\ Cardinality(OthersSeen(i)) >= (N - T)
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ sent' = sent \cup {<<i, "ECHO">>}
  /\ UNCHANGED <<corr, faulty, seen>>

LateAccept(i) ==
  /\ i \in corr
  /\ pc[i] = "echoed"
  /\ Cardinality(OthersSeen(i)) >= (N - T)
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ UNCHANGED <<corr, faulty, seen, sent>>

CloseStep ==
  /\ \A i \in 1..N : pc[i] \in {"echoed", "accepted"}
  /\ UNCHANGED vars

Next ==
  \/ \E i \in 1..N : Receive(i)
  \/ \E i \in 1..N : SendEcho(i)
  \/ \E i \in 1..N : EchoBeforeAccept(i)
  \/ \E i \in 1..N : EchoAndAccept(i)
  \/ \E i \in 1..N : LateAccept(i)
  \/ CloseStep

TypeOK ==
  /\ corr \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> {"broadcast", "nobroadcast", "echoed", "accepted"}]
  /\ seen \in [1..N -> SUBSET (1..N \times {"ECHO"})]
  /\ sent \subseteq (1..N \times {"ECHO"})

FCConstraints ==
  /\ Cardinality(corr) = N - F
  /\ faulty = (1..N) \ corr
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

CorrLtl == <>(\A i \in 1..N : i \in corr => pc[i] = "accepted")
RelayLtl == (<>\E i \in 1..N : pc[i] = "accepted") ~> (\A i \in 1..N : pc[i] = "accepted")
UnforgLtl == (\A i \in 1..N : pc[i] \in {"nobroadcast", "echoed", "accepted"}) ~> (\A i \in 1..N : pc[i] \in {"nobroadcast", "echoed"})
Spec ==
  /\ InitAll
  /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..N : Receive(i))
  /\ WF_vars(\E i \in 1..N : SendEcho(i))
  /\ WF_vars(\E i \in 1..N : EchoBeforeAccept(i))
  /\ WF_vars(\E i \in 1..N : EchoAndAccept(i))
  /\ WF_vars(\E i \in 1..N : LateAccept(i))

====