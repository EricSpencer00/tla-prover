---- MODULE MCBakery ----
EXTENDS Naturals

\* MCBakery mirrors the Bakery specification but replaces the infinite Nat type
\* with a finite range 0..MaxNat, so a bounded model check terminates. The
\* inductive spec ISpec starts from an arbitrary type-correct state; the
\* invariant Inv then keeps every reachable state within the finite bound.

CONSTANTS N, MaxNat

VARIABLES ticket, inCS, waiting, served, bound

vars == <<ticket, inCS, waiting, served, bound>>

StateSpace == 0..MaxNat

Init ==
  /\ ticket = [i \in 1..N |-> 0]
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ waiting = [i \in 1..N |-> FALSE]
  /\ served = [i \in 1..N |-> 0]
  /\ bound = 0

\* The ticket request is capped at the finite bound MaxNat for model checking.
Request(i) ==
  /\ ~waiting[i]
  /\ ~inCS[i]
  /\ waiting' = [waiting EXCEPT ![i] = TRUE]
  /\ ticket' = [ticket EXCEPT ![i] =
        IF \E j \in 1..N : ticket[j] < MaxNat THEN ticket[i] + 1 ELSE MaxNat]
  /\ UNCHANGED <<inCS, served, bound>>

Enter(i) ==
  /\ waiting[i]
  /\ \A j \in 1..N : ~inCS[j]
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ waiting' = [waiting EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<ticket, served, bound>>

Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ served' = [served EXCEPT ![i] = bound]
  /\ bound' = IF bound < MaxNat THEN bound + 1 ELSE bound
  /\ UNCHANGED <<ticket, waiting>>

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)

Spec == Init /\ [][Next]_vars

\* The inductive spec starts from an arbitrary type-correct state; Win is the
\* constraint that state must respect.
ISpec ==
  /\ \E ticket \in [1..N -> StateSpace], inCS \in [1..N -> BOOLEAN],
       waiting \in [1..N -> BOOLEAN], served \in [1..N -> StateSpace],
       bound \in StateSpace :
       /\ MutualExclusion
       /\ TypeOK
       /\ Inv
       /\ /\ ticket' = ticket
          /\ inCS' = inCS
          /\ waiting' = waiting
          /\ served' = served
          /\ bound' = bound
  /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => i = j

TypeOK ==
  /\ ticket \in [1..N -> StateSpace]
  /\ inCS \in [1..N -> BOOLEAN]
  /\ waiting \in [1..N -> BOOLEAN]
  /\ served \in [1..N -> StateSpace]
  /\ bound \in StateSpace

Inv ==
  /\ bound = MaxNat
  /\ \A i \in 1..N : ticket[i] <= bound

\* The .cfg file overrides the Nat operator from Naturals with NatOverride,
\* which is a finite version of Nat.  Nat is kept from Naturals, but the
\* .cfg replacement must only ever rename Nat to NatOverride, never declare Nat.
NatOverride == StateSpace

====