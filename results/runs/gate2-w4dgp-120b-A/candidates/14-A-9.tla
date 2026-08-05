---- MODULE MCBoulanger ----
EXTENDS Integers, Naturals

CONSTANTS N, MaxNat

ASSUME N \in Nat \ {0}

VARIABLES ticket, next, nserved, cs
vars == <<ticket, next, nserved, cs>>

TypeOK ==
  /\ ticket \in [0..(N - 1) -> 0..MaxNat]
  /\ next \in 0..N
  /\ nserved \in 0..N
  /\ cs \in [0..(N - 1) -> BOOLEAN]

Init ==
  /\ ticket = [i \in 0..(N - 1) |-> 0]
  /\ next = 0
  /\ nserved = 0
  /\ cs = [i \in 0..(N - 1) |-> FALSE]

Request(i) ==
  /\ ~cs[i]
  /\ next < N
  /\ ticket' = [ticket EXCEPT ![i] = next]
  /\ next' = next + 1
  /\ UNCHANGED <<nserved, cs>>

Enter(i) ==
  /\ ~cs[i]
  /\ \A k \in 0..(N - 1) : ticket[i] <= ticket[k] \/ ~cs[k]
  /\ cs' = [cs EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<ticket, next, nserved>>

Exit(i) ==
  /\ cs[i]
  /\ cs' = [cs EXCEPT ![i] = FALSE]
  /\ nserved' = nserved + 1
  /\ UNCHANGED <<ticket, next>>

Next ==
  \/ \E i \in 0..(N - 1) : Request(i)
  \/ \E i \in 0..(N - 1) : Enter(i)
  \/ \E i \in 0..(N - 1) : Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i \in 0..(N - 1), j \in 0..(N - 1) : (cs[i] /\ cs[j]) => i = j

Inv ==
  /\ nserved <= N
  /\ next >= nserved
  /\ \A i \in 0..(N - 1) : cs[i] => ticket[i] < next

NatOverride ==
  Nat = {n \in Nat : n <= MaxNat}

StateBounded ==
  \A i \in 0..(N - 1) : ticket[i] < MaxNat
====