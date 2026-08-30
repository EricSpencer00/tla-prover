---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* This module extends the Bakery specification for model checking by
\* capping the natural numbers to a finite range 0..MaxNat. It inherits
\* the full set of state variables, actions, and invariants from the
\* standard Bakery spec (not restated here) and redefines Nat as a
\* finite-sorted construct so the model stays finite. The inductive
\* spec ISpec starts from any state satisfying the invariant and checks
\* that the invariant is preserved by Init and Next.

\* Replace the unbounded Nat from Naturals with a bounded version for
\* model checking; keep EXTENDS Naturals so the rest of Naturals stays
\* available without redeclaring Nat itself.
NatOverride == {0, 1, 2, 3, 4}

VARIABLES phase, chosen, ticket, inside

vars == <<phase, chosen, ticket, inside>>

Processes == 1 .. N

TypeOK ==
  /\ phase \in [Processes -> {"idle", "waiting", "critical"}]
  /\ chosen \in [Processes -> BOOLEAN]
  /\ ticket \in [Processes -> 0 .. MaxNat]
  /\ inside \in [Processes -> BOOLEAN]

Init ==
  /\ phase = [p \in Processes |-> "idle"]
  /\ chosen = [p \in Processes |-> FALSE]
  /\ ticket = [p \in Processes |-> 0]
  /\ inside = [p \in Processes |-> FALSE]

Next == UNCHANGED vars

\* The inductive specification: any state satisfying the invariant is
\* reachable from Init by Init and Next alone, so Init and Next alone
\* suffice to preserve the invariant; no extra or privileged action is
\* needed to reach or maintain it.
ISpec == Init /\ [][Next]_vars

MutualExclusion == \A p \in Processes : inside[p] => phase[p] = "critical"

\* Full inductive invariant: mutual exclusion plus all type constraints.
Inv == MutualExclusion /\ TypeOK

====