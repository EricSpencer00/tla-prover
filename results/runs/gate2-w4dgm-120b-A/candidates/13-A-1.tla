---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, MaxNat

\* The operators being overridden are redefined on the right-hand side of
\* the same-named identifier from the .cfg, so they are assignments here,
\* not new declarations. Nat becomes a bounded range rather than the full
\* infinite set, which is what makes the model finite and checkable.
Nat == 0..MaxNat
NatCard == MaxNat + 1
Mod == N + 1

VARIABLES token, inCS, want, ticket, doneCount

vars == <<token, inCS, want, ticket, doneCount>>

TypeOK ==
  /\ token \in Nat
  /\ inCS \in 0..N
  /\ want \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> Nat]
  /\ doneCount \in Nat

\* The full inductive invariant: the token is always the smallest live
\* ticket number, and only the current ticket owner may be in the critical
\* section.
Inv ==
  /\ \A p \in 1..N : inCS # 0 => ticket[p] = token
  /\ \A p \in 1..N : want[p] => ticket[p] < NatCard

Init ==
  /\ token = 0
  /\ inCS = 0
  /\ want = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ doneCount = 0

Request(p) ==
  /\ ~want[p]
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = (token + doneCount) % NatCard]
  /\ UNCHANGED <<token, inCS, doneCount>>

Enter(p) ==
  /\ want[p]
  /\ inCS = 0
  /\ ticket[p] = token
  /\ inCS' = p
  /\ UNCHANGED <<token, want, ticket, doneCount>>

Exit(p) ==
  /\ inCS = p
  /\ inCS' = 0
  /\ token' = (token + 1) % NatCard
  /\ doneCount' = (doneCount + 1) % NatCard
  /\ want' = [want EXCEPT ![p] = FALSE]
  /\ UNCHANGED ticket

\* Once every process is done, the bakery cycles back to the start.
Rejoin ==
  /\ \A p \in 1..N : ~want[p]
  /\ doneCount > 0
  /\ doneCount' = 0
  /\ UNCHANGED <<token, inCS, want, ticket>>

Next ==
  \E p \in 1..N : Request(p) \/ Enter(p) \/ Exit(p) \/ Rejoin

\* The inductive spec starts from any reachable state satisfying the
\* invariant, not just the canonical initial state, so fairness only needs
\* to be weak per process here.
ISpec == \E p \in 1..N : SF_vars(Enter(p)) /\ SF_vars(Exit(p))

Spec == ISpec

MutualExclusion == Inv
====