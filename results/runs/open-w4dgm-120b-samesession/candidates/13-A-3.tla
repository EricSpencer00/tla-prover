---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES entering, critical, idle, target, num, using

vars == <<entering critical, idle, target, num, using>>

TypeOK ==
  /\ entering \in [1..N -> BOOLEAN]
  /\ critical \in [1..N -> BOOLEAN]
  /\ idle \in [1..N -> BOOLEAN]
  /\ target \in [1..N -> 0..N]
  /\ num \in [1..N -> 0..MaxNat]
  /\ using \in [1..N -> 0..MaxNat]

MutualExclusion ==
  \A i, j \in 1..N : (critical[i] /\ critical[j]) => i = j

Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ \A i \in 1..N : entering[i] => ~idle[i]
  /\ \A i \in 1..N : critical[i] => (entering[i] /\ ~idle[i])
  /\ \A i \in 1..N : idle[i] => (~entering[i] /\ ~critical[i])
  /\ \A i \in 1..N : ~using[i] => (num[i] = 0 /\ target[i] = 0)

Init ==
  /\ entering = [i \in 1..N |-> FALSE]
  /\ critical = [i \in 1..N |-> FALSE]
  /\ idle = [i \in 1..N |-> TRUE]
  /\ target = [i \in 1..N |-> 0]
  /\ num = [i \in 1..N |-> 0]
  /\ using = [i \in 1..N |-> FALSE]

Begin(i, j) ==
  /\ idle[i]
  /\ i # j
  /\ \A k \in 1..N : ~using[k]
  /\ idle' = [idle EXCEPT ![i] = FALSE]
  /\ entering' = [entering EXCEPT ![i] = TRUE]
  /\ target' = [target EXCEPT ![i] = j]
  /\ using' = [using EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<critical, num>>

Enter(i) ==
  /\ entering[i]
  /\ ~critical[i]
  /\ \A k \in 1..N : ~critical[k]
  /\ critical' = [critical EXCEPT ![i] = TRUE]
  /\ num' = [num EXCEPT ![i] = IF num[i] < MaxNat THEN num[i] + 1 ELSE num[i]]
  /\ UNCHANGED <<entering, idle, target, using>>

Leave(i) ==
  /\ critical[i]
  /\ critical' = [critical EXCEPT ![i] = FALSE]
  /\ using' = [using EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<entering, idle, target, num>>

GoingIdle(i) ==
  /\ ~entering[i]
  /\ ~critical[i]
  /\ ~using[i]
  /\ ~idle[i]
  /\ idle' = [idle EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<entering, critical, target, num, using>>

Next ==
  \/ \E i \in 1..N, j \in 1..N : Begin(i, j)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Leave(i)
  \/ \E i \in 1..N : GoingIdle(i)

ISpec == Init /\ [][Next]_vars

====