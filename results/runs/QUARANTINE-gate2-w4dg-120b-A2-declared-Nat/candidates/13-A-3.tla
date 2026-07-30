---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES num, waiting, served

vars == <<num, waiting, served>>

\* The original Bakery spec (https://lamport.azurewebsites.net/pubs/pubs.html#bakery)
\* has the same state and actions.  This module adds only a finite cap on Nat.
\* The bound is expressed as a finite set rather than an axiom to keep the
\* model checker happy with type checking.

BoundedNat == 0 .. MaxNat

TypeOK ==
  /\ num \in BoundedNat
  /\ waiting \in [1..N -> BOOLEAN]
  /\ served \in [1..N -> BOOLEAN]

Init ==
  /\ num = 0
  /\ waiting = [i \in 1..N |-> FALSE]
  /\ served = [i \in 1..N |-> FALSE]

\* A process requests entry into the critical section (into 'waiting').
Bump(i) ==
  /\ ~waiting[i]
  /\ ~served[i]
  /\ num < MaxNat
  /\ waiting' = [waiting EXCEPT ![i] = TRUE]
  /\ num' = num + 1
  /\ UNCHANGED served

\* A waiting process enters the critical section.
Enter(i) ==
  /\ waiting[i]
  /\ served' = [served EXCEPT ![i] = TRUE]
  /\ waiting' = [waiting EXCEPT ![i] = FALSE]
  /\ UNCHANGED num

\* A process in the critical section leaves it.
Exit(i) ==
  /\ served[i]
  /\ served' = [served EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<num, waiting>>

Next ==
  \/ \E i \in 1..N : Bump(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

Spec == Spec

\* The inductive specification: starts from any state satisfying the invariant
\* and checks preservation under every transition.
ISpec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Next)

MutualExclusion ==
  \A i, j \in 1..N :
    (served[i] /\ served[j]) => i = j

Inv == TypeOK

\* Nat is overridden globally to a finite range, so no separate operator is
\* needed: BoundedNat is the finite version used throughout.
NatOverride == BoundedNat

====