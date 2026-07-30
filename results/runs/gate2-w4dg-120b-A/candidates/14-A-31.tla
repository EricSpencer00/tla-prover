---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* Finite bound: the natural-number type is overridden with a range 0..MaxNat
\* and a state constraint prunes states whose tickets would exceed MaxNat-1.
Numbers == 0 .. MaxNat

VARIABLES pc, ticket, serving

vars == << pc, ticket, serving >>

Bump(x) == (x + 1) % (MaxNat + 1)

Init ==
  /\ pc = [i \in 1 .. N |-> "idle"]
  /\ ticket = [i \in 1 .. N |-> 0]
  /\ serving = 0

Acquire(i) ==
  /\ pc[i] = "idle"
  /\ ticket' = [ticket EXCEPT ![i] = Bump(@)]
  /\ pc' = [pc EXCEPT ![i] = "trying"]
  /\ UNCHANGED serving

Enter(i) ==
  /\ pc[i] = "trying"
  /\ serving = 0
  /\ serving' = i
  /\ pc' = [pc EXCEPT ![i] = "critical"]
  /\ UNCHANGED ticket

Exit(i) ==
  /\ pc[i] = "critical"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ serving' = 0
  /\ UNCHANGED ticket

Next ==
  \/ \E i \in 1 .. N : Acquire(i)
  \/ \E i \in 1 .. N : Enter(i)
  \/ \E i \in 1 .. N : Exit(i)

Spec == Init /\ [][Next]_vars

\* Bounded range for natural numbers; no ticket may reach the maximum.
NatRange == \A i \in 1 .. N : ticket[i] < MaxNat

MutualExclusion == serving /= 0 => pc[serving] = "critical"

TypeOK ==
  /\ pc \in [1 .. N -> {"idle", "trying", "critical"}]
  /\ ticket \in [1 .. N -> Numbers]
  /\ serving \in 0 .. N

Inv == MutualExclusion /\ TypeOK

====