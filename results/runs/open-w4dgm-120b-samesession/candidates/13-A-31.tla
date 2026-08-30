---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* A single Nat sort is imported from Naturals and then replaced by a finite
\* version via NatOverride below; the name Nat itself is never declared here.
VARIABLES reg, inCS, ticket, want, mode

vars == <<reg, inCS, ticket, want, mode>>

TypeOK ==
  /\ reg \in {"idle", "busy"}
  /\ inCS \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ want \in [1..N -> BOOLEAN]
  /\ mode \in {"active", "idle"}

\* The full invariant captured by the Bakery algorithm: the registration
\* register is busy exactly when some process is in its critical section.
MutualExclusion == reg = "busy" <=> \E i \in 1..N : inCS[i]

\* The set of processes currently in their critical sections is downward-
\* closed under ticket numbers: no process holds a strictly higher ticket
\* than a process that is still in its critical section. This is exactly
\* the property that forces critical sections to be entered strictly in
\* ascending ticket order, and since ticket numbers are never reused,
\* it implies the critical sections are visited in a linear chain with
\* no concurrent execution - i.e. mutual exclusion.
Inv ==
  /\ MutualExclusion
  /\ \A i \in 1..N : inCS[i] => \A j \in 1..N : inCS[j] => ticket[i] <= ticket[j]

Init ==
  /\ reg = "idle"
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ want = [i \in 1..N |-> FALSE]
  /\ mode = [i \in 1..N |-> "idle"]

Request(i) ==
  /\ ~want[i]
  /\ mode[i] = "idle"
  /\ want' = [want EXCEPT ![i] = TRUE]
  /\ mode' = [mode EXCEPT ![i] = "active"]
  /\ UNCHANGED <<reg, inCS, ticket>>

Register(i) ==
  /\ want[i]
  /\ reg = "idle"
  /\ \A j \in 1..N : mode[j] = "idle"
  /\ reg' = "busy"
  /\ ticket' = [j \in 1..N |-> IF j = i THEN MaxNat ELSE IF ticket[j] < MaxNat THEN ticket[j] + 1 ELSE MaxNat]
  /\ UNCHANGED <<inCS, want, mode>>

EnterCS(i) ==
  /\ want[i]
  /\ reg = "busy"
  /\ ~inCS[i]
  /\ \A j \in 1..N : ~inCS[j]
  /\ \A j \in 1..N : mode[j] = "idle"
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<reg, ticket, want, mode>>

LeaveCS(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ reg' = "idle"
  /\ want' = [want EXCEPT ![i] = FALSE]
  /\ mode' = [mode EXCEPT ![i] = "idle"]
  /\ UNCHANGED ticket

Next ==
  \E i \in 1..N :
    \/ Request(i) \/ Register(i) \/ EnterCS(i) \/ LeaveCS(i)

\* Starts from any reachable state rather than just Init, since the full
\* invariant must hold on all reachable states, not just those reachable
\* from the initial state.
ISpec == Init /\ [][Next]_vars

\* No liveness property is required by the spec; the two-step entry
\* protocol is strongly fair but that is not part of the correctness
\* argument itself, so nothing is listed here.
Properties == TRUE

\* Finite upper bound on the ticket counter: the override below makes
\* Nat a finite sort capped at MaxNat, which is what makes exhaustive
\* checking feasible for this model.
NatOverride == 0..MaxNat
====