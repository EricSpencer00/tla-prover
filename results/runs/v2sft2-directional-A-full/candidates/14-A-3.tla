---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS
\* ----------------------------------------------------------------------
CONSTANT N, MaxNat, Nat

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
\* The finite range of natural numbers for this model
Nat == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* State variables (inherited from Boulanger)
\* ----------------------------------------------------------------------
VARIABLES owner, ticket, next

\* ----------------------------------------------------------------------
\* Type correctness (required invariant)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ owner \in 0 .. N
    /\ ticket \in [1 .. N -> Nat]
    /\ next \in Nat

\* ----------------------------------------------------------------------
\* Mutual exclusion invariant (required invariant)
\* ----------------------------------------------------------------------
MutualExclusion ==
    \A i, j \in 1 .. N : (i # j => owner[i] # owner[j])

\* ----------------------------------------------------------------------
\* Full inductive invariant (required invariant)
\* ----------------------------------------------------------------------
Inv ==
    TypeOK /\ MutualExclusion

\* ----------------------------------------------------------------------
\* Initial state (same as Boulanger spec)
\* ----------------------------------------------------------------------
Init ==
    /\ owner = 0
    /\ ticket = [i \in 1 .. N |-> 0]
    /\ next = 0

\* ----------------------------------------------------------------------
\* Request action for a process i
\* ----------------------------------------------------------------------
Request(i) ==
    /\ i \in 1 .. N
    /\ ticket[i] = 0
    /\ ticket' = [ticket EXCEPT ![i] = next]
    /\ next' = next + 1
    /\ UNCHANGED owner

\* ----------------------------------------------------------------------
\* Acquire action when the process has the smallest ticket
\* ----------------------------------------------------------------------
Acquire(i) ==
    /\ i \in 1 .. N
    /\ ticket[i] > 0
    /\ \A j \in 1 .. N :
          j # i => ticket[j] >= ticket[i]
    /\ owner' = i
    /\ UNCHANGED <<ticket, next>>

\* ----------------------------------------------------------------------
\* Release action
\* ----------------------------------------------------------------------
Release(i) ==
    /\ i = owner
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ owner' = 0
    /\ UNCHANGED next

\* ----------------------------------------------------------------------
\* Next-state relation (union of all actions)
\* ----------------------------------------------------------------------
Next ==
    \/ \E i \in 1 .. N : Request(i)
    \/ \E i \in 1 .. N : Acquire(i)
    \/ \E i \in 1 .. N : Release(i)

\* ----------------------------------------------------------------------
\* Specification (required)
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<owner, ticket, next>>

\* ----------------------------------------------------------------------
\* State constraint (prevents tickets from reaching MaxNat)
\* ----------------------------------------------------------------------
StateConstraint ==
    \A i \in 1 .. N : ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\* The CHECK_STATE_CONSTRAINT pragma tells TLC to enforce the constraint
\* during exploration, pruning any state where a ticket would be >= MaxNat.
\* ----------------------------------------------------------------------
CHECK_STATE_CONSTRAINT StateConstraint

====