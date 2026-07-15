---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

\* ==============================================================================
\* Types
\* ==============================================================================
TyProc == 1..N
TyNat  == Nat

\* ==============================================================================
\* State variables (inherited from Bakery specification)
\* ==============================================================================
VARIABLES pc, ticket, next

\* ==============================================================================
\* Helper definitions
\* ==============================================================================
\* The finite set Nat overrides the infinite set of natural numbers.
NatRange == 0..MaxNat

\* ==============================================================================
\* Initial state
\* ==============================================================================
Init ==
  /\ pc = [i \in TyProc |-> "idle"]
  /\ ticket = [i \in TyProc |-> 0]
  /\ next = 0

\* ==============================================================================
\* Actions (derived from the standard Bakery algorithm)
\* ==============================================================================
Aquire(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ ticket' = [ticket EXCEPT ![i] = next]
  /\ next' = (next + 1) % (MaxNat + 1)
  /\ UNCHANGED << >>

Wait(i) ==
  /\ pc[i] = "wait"
  /\ \A j \in TyProc :
        (j # i) =>
          ~(
            /\ pc[j] = "cs"
            /\ (ticket[j] < ticket[i] \/ (ticket[j] = ticket[i] /\ j < i))
          )
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << ticket, next >>

Release(i) ==
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED next

Next ==
  \E i \in TyProc :
    Aquire(i) \/ Wait(i) \/ Release(i)

\* ==============================================================================
\* Specification (inductive, allowing any type‑correct state satisfying the invariant)
\* ==============================================================================
IsInit == Init
IsNext == Next

\* The specification required by the configuration file
ISpec == Init /\ [] [Next]_<<pc, ticket, next>>

\* ==============================================================================
\* Invariants
\* ==============================================================================
MutualExclusion ==
  \A i, j \in TyProc :
    (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

TypeOK ==
  /\ pc \in [TyProc -> {"idle", "wait", "cs"}]
  /\ ticket \in [TyProc -> NatRange]
  /\ next \in NatRange

Inv == MutualExclusion /\ TypeOK

\* ==============================================================================
\* Theorems (optional, for TLC to recognize invariants if needed)
\* ==============================================================================
THEOREM Init => TypeOK

====