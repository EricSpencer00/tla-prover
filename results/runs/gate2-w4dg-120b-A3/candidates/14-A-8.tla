---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES cs, waiting, ticks, served
vars == <<cs, waiting, ticks, served>>

Init ==
  /\ cs = 0
  /\ waiting = [p \in 1..N |-> FALSE]
  /\ ticks = [p \in 1..N |-> 0]
  /\ served = 0

Want(p) ==
  /\ ~waiting[p]
  /\ cs = 0
  /\ waiting' = [waiting EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<cs, ticks, served>>

Enter(p) ==
  /\ waiting[p]
  /\ cs = 0
  /\ cs' = p
  /\ waiting' = [waiting EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<ticks, served>>

Exit(p) ==
  /\ cs = p
  /\ cs' = 0
  /\ served' = (served + 1) % (MaxNat + 1)
  /\ UNCHANGED <<waiting, ticks>>

Tick(p) ==
  /\ ticks' = [ticks EXCEPT ![p] = (ticks[p] + 1) % (MaxNat + 1)]
  /\ UNCHANGED <<cs, waiting, served>>

Next ==
  \/ \E p \in 1..N: Want(p)
  \/ \E p \in 1..N: Enter(p)
  \/ \E p \in 1..N: Exit(p)
  \/ \E p \in 1..N: Tick(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p \in 1..N : (cs = p) => (\A q \in 1..N : (cs = q) => q = p)

TypeOK ==
  /\ cs \in 0..N
  /\ waiting \in [1..N -> BOOLEAN]
  /\ ticks \in [1..N -> 0..MaxNat]
  /\ served \in 0..MaxNat

Inv ==
  /\ MutualExclusion
  /\ TypeOK

NatOverride == Nat

====