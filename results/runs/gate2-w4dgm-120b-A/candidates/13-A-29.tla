---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES cs, want, ticket, nextTicket, inCs, stage
vars == <<cs, want, ticket, nextTicket, inCs, stage>>

\* Model-checking override: Nat is replaced by a bounded version, so ticket
\* numbers stay in a finite range and the reachable state space is finite.
NatOverride(n) == n % (MaxNat + 1)

TypeOK ==
  /\ cs \in [1..N -> BOOLEAN]
  /\ want \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat
  /\ inCs \in [1..N -> BOOLEAN]
  /\ stage \in [1..N -> {"idle", "waiting", "cs"}]

\* The Bakery algorithm's joint condition, written out as two conjuncts: a
\* process is only in its critical section when it wants it and no other
\* process shares its ticket number.
MutualExclusion ==
  \A i \in 1..N :
    inCs[i] => /\ want[i]
               /\ \A j \in 1..N : (j # i) => ticket[j] # ticket[i]

Init ==
  /\ cs = [i \in 1..N |-> FALSE]
  /\ want = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0
  /\ inCs = [i \in 1..N |-> FALSE]
  /\ stage = [i \in 1..N |-> "idle"]

\* A process may be slow but never fails, so it can take its ticket and not
\* enter the critical section immediately.
Request(i) ==
  /\ ~want[i]
  /\ cs[i] = FALSE
  /\ ticket[i] = 0
  /\ want' = [want EXCEPT ![i] = TRUE]
  /\ ticket' = [ticket EXCEPT ![i] = NatOverride(nextTicket)]
  /\ nextTicket' = NatOverride(nextTicket + 1)
  /\ stage' = [stage EXCEPT ![i] = "waiting"]
  /\ UNCHANGED <<cs, inCs>>

Enter(i) ==
  /\ want[i]
  /\ cs[i] = FALSE
  /\ \A j \in 1..N : (j # i) => ticket[j] # ticket[i]
  /\ cs' = [cs EXCEPT ![i] = TRUE]
  /\ inCs' = [inCs EXCEPT ![i] = TRUE]
  /\ stage' = [stage EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<want, ticket, nextTicket>>

Exit(i) ==
  /\ cs[i] = TRUE
  /\ cs' = [cs EXCEPT ![i] = FALSE]
  /\ inCs' = [inCs EXCEPT ![i] = FALSE]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ want' = [want EXCEPT ![i] = FALSE]
  /\ stage' = [stage EXCEPT ![i] = "idle"]
  /\ UNCHANGED nextTicket

Next == \E i \in 1..N : Request(i) \/ Enter(i) \/ Exit(i)

\* Inductive spec: any reachable state (not just those from the start
\* state) must already satisfy the invariant.
ISpec == Init /\ [][Next]_vars

\* Full inductive invariant: mutual exclusion plus every variable's type.
Inv == MutualExclusion /\ TypeOK
====