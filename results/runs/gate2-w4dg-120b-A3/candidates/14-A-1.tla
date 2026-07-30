---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Nat is inherited from Naturals; NatOverride replaces it as a FINITE
\* version for this model, so Nat itself is never declared here.
NatOverride == {0 .. (MaxNat - 1)}

VARIABLES pstate, ticket, pc, count
vars == <<pstate, ticket, pc, count>>

Phases == {"idle", "trying", "critical", "holding"}

Init ==
  /\ pstate = [p \in 0 .. (N - 1) |-> "idle"]
  /\ ticket = [p \in 0 .. (N - 1) |-> 0]
  /\ pc = [p \in 0 .. (N - 1) |-> 1]
  /\ count = [p \in 0 .. (N - 1) |-> 0]

\* Action names are exactly the same as in the Boulanger spec and are
\* deliberately left unchanged here.
Request(p) ==
  /\ pstate[p] = "idle"
  /\ pstate' = [pstate EXCEPT ![p] = "trying"]
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED count

Increment(p) ==
  /\ pstate[p] = "trying"
  /\ pc[p] = 1
  /\ \A q \in 0 .. (N - 1) : pstate[q] # "critical"
  /\ count[p] < (MaxNat - 1)
  /\ ticket' = [ticket EXCEPT ![p] = count[p]]
  /\ count' = [count EXCEPT ![p] = count[p] + 1]
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED pstate

Enter(p) ==
  /\ pstate[p] = "trying"
  /\ pc[p] = 2
  /\ \A q \in 0 .. (N - 1) : pstate[q] # "critical"
  /\ pstate' = [pstate EXCEPT ![p] = "critical"]
  /\ UNCHANGED <<ticket, pc, count>>

Exit(p) ==
  /\ pstate[p] = "critical"
  /\ pstate' = [pstate EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<ticket, pc, count>>

Next ==
  \/ \E p \in 0 .. (N - 1) : Request(p)
  \/ \E p \in 0 .. (N - 1) : Increment(p)
  \/ \E p \in 0 .. (N - 1) : Enter(p)
  \/ \E p \in 0 .. (N - 1) : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p \in 0 .. (N - 1) : \A q \in 0 .. (N - 1) :
    (pstate[p] = "critical" /\ pstate[q] = "critical") => (p = q)

TypeOK ==
  /\ pstate \in [0 .. (N - 1) -> Phases]
  /\ ticket \in [0 .. (N - 1) -> NatOverride]
  /\ pc \in [0 .. (N - 1) -> 0 .. 2]
  /\ count \in [0 .. (N - 1) -> 0 .. MaxNat]

Inv ==
  /\ MutualExclusion
  /\ TypeOK

StateConstraint == \A p \in 0 .. (N - 1) : ticket[p] < MaxNat

====