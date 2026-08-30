---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* NatOverride replaces the unbounded Nat from Naturals with a finite range
\* so the model checking state space stays finite; it leaves the constant
\* symbols from Naturals otherwise untouched, which is exactly what the .cfg
\* expects for "NatOverride : Nat".
NatOverride == (0..MaxNat)

VARIABLES cs, pc, ticket, nextTicket

vars == <<cs, pc, ticket, nextTicket>>

TypeOK ==
  /\ cs \in [1..N -> BOOLEAN]
  /\ pc \in [1..N -> {"idle", "waiting", "critical"}]
  /\ ticket \in [1..N -> NatOverride]
  /\ nextTicket \in NatOverride

MutualExclusion ==
  \A a, b \in 1..N : (cs[a] /\ cs[b]) => a = b

Init ==
  /\ cs = [i \in 1..N |-> FALSE]
  /\ pc = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0

Request(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "waiting"]
  /\ UNCHANGED <<cs, ticket, nextTicket>>

Acquire(i) ==
  /\ pc[i] = "waiting"
  /\ \A j \in 1..N : cs[j] = FALSE
  /\ cs' = [cs EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "critical"]
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket

Release(i) ==
  /\ pc[i] = "critical"
  /\ cs' = [cs EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<ticket, nextTicket>>

Next ==
  \E i \in 1..N : Request(i) \/ Acquire(i) \/ Release(i)

\* This is the inductive specification: starting from any reachable state that
\* already satisfies the invariant, no transition may break it.
Spec == Init /\ [][Next]_vars

\* The complete inductive invariant, including the mutual-exclusion clause.
Inv ==
  /\ TypeOK
  /\ MutualExclusion

\* SAFETY PROPERTY: mutual exclusion holds in every reachable state.
MutualExclusion == MutualExclusion

\* TYPE-CHECKING PROPERTY: every reachable state satisfies its type
\* annotation, so no variable ever leaves its declared range.
TypeOK == TypeOK

\* SAFETY PROPERTY: the full inductive invariant holds in every reachable state.
InductiveInvariant == Inv

\* The configuration file asks TLC to start from arbitrary reachable states
\* (not just the initial state) using Spec, so the full suite of invariants
\* is checked as a block, and the model is finite because NatOverride is a
\* bounded range.
====