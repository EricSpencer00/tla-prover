---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES coarse, fine, cs, ticket, want, slow

vars == <<coarse, fine, cs, ticket, want, slow>>

\* Finite range for natural numbers, overriding the unbounded Naturals type
NatOverride == 0..MaxNat

Init ==
  /\ coarse = "free"
  /\ fine = "free"
  /\ cs = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ want = [p \in 1..N |-> FALSE]
  /\ slow = {}

AcquireCoarse(p) ==
  /\ want[p]
  /\ coarse = "free"
  /\ coarse' = "coarse_" \o p
  /\ UNCHANGED <<fine, cs, ticket, want, slow>>

AcquireFine(p) ==
  /\ coarse = "coarse_" \o p
  /\ fine = "free"
  /\ fine' = "fine_" \o p
  /\ UNCHANGED <<coarse, cs, ticket, want, slow>>

Enter(p) ==
  /\ coarse = "coarse_" \o p
  /\ fine = "fine_" \o p
  /\ cs' = [cs EXCEPT ![p] = "cs"]
  /\ ticket' = [ticket EXCEPT ![p] = IF @ < MaxNat THEN @ + 1 ELSE @]
  /\ UNCHANGED <<coarse, fine, want, slow>>

Exit(p) ==
  /\ cs[p] = "cs"
  /\ cs' = [cs EXCEPT ![p] = "idle"]
  /\ coarse' = "free"
  /\ fine' = "free"
  /\ UNCHANGED <<ticket, want, slow>>

Request(p) ==
  /\ ~want[p]
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<coarse, fine, cs, ticket, slow>>

SlowStep(p) ==
  /\ p \notin slow
  /\ slow' = slow \cup {p}
  /\ UNCHANGED <<coarse, fine, cs, ticket, want>>

ResetSlow(p) ==
  /\ p \in slow
  /\ slow' = slow \ {p}
  /\ UNCHANGED <<coarse, fine, cs, ticket, want>>

Next ==
  \/ \E p \in 1..N : AcquireCoarse(p) \/ AcquireFine(p) \/ Enter(p)
  \/ \E p \in 1..N : Exit(p) \/ Request(p) \/ SlowStep(p) \/ ResetSlow(p)

Spec == Init /\ [][Next]_vars

\* SAFETY: mutual exclusion, type correctness, and the full inductive invariant
MutualExclusion == \A p \in 1..N : cs[p] = "cs" => fine = "fine_" \o p
TypeOK ==
  /\ coarse \in {"free"} \cup { "coarse_" \o p : p \in 1..N }
  /\ fine \in {"free"} \cup { "fine_" \o p : p \in 1..N }
  /\ cs \in [1..N -> {"idle", "cs"}]
  /\ ticket \in [1..N -> NatOverride]
  /\ want \in [1..N -> BOOLEAN]
  /\ slow \subseteq (1..N)
Inv ==
  \A p \in 1..N :
    /\ (cs[p] = "cs" => (coarse = "coarse_" \o p /\ fine = "fine_" \o p))
    /\ (fine = "fine_" \o p => coarse = "coarse_" \o p)
    /\ (cs[p] = "cs" => p \notin slow)

\* LIVENESS: NOT_SPECIFIED

====