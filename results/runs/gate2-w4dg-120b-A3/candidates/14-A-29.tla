---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES cs1, cs2, pl, tickets
vars == <<cs1, cs2, pl, tickets>>

RECURSIVE MaxNatUpTo(_)
MaxNatUpTo(n) == IF n = 0 THEN 0 ELSE IF n > MaxNat THEN MaxNat ELSE n

Init ==
  /\ cs1 = [i \in 1..N |-> "idle"]
  /\ cs2 = [i \in 1..N |-> "idle"]
  /\ pl = 0
  /\ tickets = [i \in 1..N |-> 0]

Enter(i) ==
  /\ cs1[i] = "idle"
  /\ cs1' = [cs1 EXCEPT ![i] = "trying"]
  /\ tickets' = [tickets EXCEPT ![i] = MaxNatUpTo(pl)]
  /\ pl' = MaxNatUpTo(pl + 1)
  /\ UNCHANGED cs2

Lock(i) ==
  /\ cs1[i] = "trying"
  /\ cs2' = [cs2 EXCEPT ![i] = "critical"]
  /\ cs1' = [cs1 EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<pl, tickets>>

Exit(i) ==
  /\ cs2[i] = "critical"
  /\ cs2' = [cs2 EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<cs1, pl, tickets>>

Next ==
  \E i \in 1..N : Enter(i) \/ Lock(i) \/ Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in 1..N : (i # j) => ~(cs2[i] = "critical" /\ cs2[j] = "critical")

TypeOK ==
  /\ cs1 \in [1..N -> {"idle", "trying"}]
  /\ cs2 \in [1..N -> {"idle", "critical"}]
  /\ pl \in 0..MaxNat
  /\ tickets \in [1..N -> 0..MaxNat]

Inv ==
  MutualExclusion /\ TypeOK

TicketBound ==
  \A i \in 1..N : tickets[i] < MaxNat

====