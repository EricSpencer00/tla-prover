---- MODULE MCBakery ----
EXTENDS Naturals

\* A model-checking configuration module for the Bakery mutual exclusion
\* algorithm.  It re-declares the natural-number set with a finite bound
\* (NatOverride) to make the state space finite, and uses the inductive
\* specification (ISpec) rather than a purely initial-state spec.
\* Reference configuration (baked into the spec): N=2, MaxNat=2, deadlock
\* checking disabled.

CONSTANTS N, MaxNat, Nat

VARIABLES num, inCS, serving, taken
vars == <<num, inCS, serving, taken>>

TypeOK ==
  /\ num \in 0..MaxNat
  /\ inCS \subseteq 1..N
  /\ serving \subseteq 1..N
  /\ taken \subseteq 0..MaxNat

Init ==
  /\ num = 0
  /\ inCS = {}
  /\ serving = {}
  /\ taken = {}

\* A process requests entry into the critical section (only when idle).
Request(p) ==
  /\ p \notin serving
  /\ p \notin inCS
  /\ serving' = serving \cup {p}
  /\ UNCHANGED <<num, inCS, taken>>

\* A process takes a bakery ticket and enters the critical section.
Take(p) ==
  /\ p \in serving
  /\ p \notin inCS
  /\ num < MaxNat
  /\ inCS' = inCS \cup {p}
  /\ serving' = serving \ {p}
  /\ num' = num + 1
  /\ taken' = taken \cup {num}
  /\ UNCHANGED <<num, inCS, serving, taken>>

\* A process leaves the critical section.
Exit(p) ==
  /\ p \in inCS
  /\ inCS' = inCS \ {p}
  /\ UNCHANGED <<num, serving, taken>>

\* A ticket number is freed once it is no longer in use.
FreeTicket(n) ==
  /\ n \in taken
  /\ \A p \in inCS : n # (num - (Cardinality(inCS) - 1))
  /\ taken' = taken \ {n}
  /\ UNCHANGED <<num, inCS, serving, taken>>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Take(p)
  \/ \E p \in 1..N : Exit(p)
  \/ \E n \in 0..MaxNat : FreeTicket(n)

\* The inductive spec: any reachable state satisfies the invariant (type
\* correctness) and then takes a strongly fair step.
ISpec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N : Request(p))
  /\ WF_vars(\E p \in 1..N : Take(p))
  /\ WF_vars(\E p \in 1..N : Exit(p))
  /\ WF_vars(\E n \in 0..MaxNat : FreeTicket(n))
  /\ SF_vars(\E p \in 1..N : Request(p))
  /\ SF_vars(\E p \in 1..N : Take(p))
  /\ SF_vars(\E p \in 1..N : Exit(p))
  /\ SF_vars(\E n \in 0..MaxNat : FreeTicket(n))

MutualExclusion == \A p1 \in inCS, p2 \in inCS : p1 = p2

Inv == TypeOK /\ MutualExclusion

NatOverride ==
  \E f \in [Nat -> 0..MaxNat] : \A n \in Nat : n \in NatOverride

====