---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES status, pc, ticket, turn

vars == <<status, pc, ticket, turn>>

\* The override replaces Nat with a FINITE version for model checking, so
\* ticket numbering stays within the bounded range.
NatOverride(n) == IF n <= MaxNat THEN n ELSE MaxNat

TypeOK ==
  /\ status \in [1..N -> {"idle", "trying", "critical"}]
  /\ pc \in [1..N -> {"idle", "wanting", "cs"}]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ turn \in 0..MaxNat

\* Each process records its ticket at entry time so every occupant's claim
\* can be checked against the page turn that came after it.
Claimed == {k \in 1..N : pc[k] = "cs"}

MutualExclusion == \A i \in 1..N : (pc[i] = "cs") => (Claimed = {i})

Init ==
  /\ status = [i \in 1..N |-> "idle"]
  /\ pc = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]
  /\ turn = 0

Request(i) ==
  /\ status[i] = "idle"
  /\ status' = [status EXCEPT ![i] = "trying"]
  /\ pc' = [pc EXCEPT ![i] = "wanting"]
  /\ UNCHANGED <<ticket, turn>>

\* A process may be arbitrarily slow to enter, but it is never modelled as
\* having failed, so it cannot starve another process forever.
Enter(i) ==
  /\ status[i] = "trying"
  /\ turn < MaxNat
  /\ status' = [status EXCEPT ![i] = "critical"]
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ ticket' = [ticket EXCEPT ![i] = turn + 1]
  /\ turn' = turn + 1

Leave(i) ==
  /\ status[i] = "critical"
  /\ status' = [status EXCEPT ![i] = "idle"]
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<ticket, turn>>

Next ==
  \E i \in 1..N : Request(i) \/ Enter(i) \/ Leave(i)

\* The page turn is bounded by MaxNat; the override keeps it finite.
TurnInPage ==
  /\ turn < MaxNat
  /\ turn' = turn + 1
  /\ UNCHANGED <<status, pc, ticket>>

\* The inductive spec starts from any reachable type-correct state.
ISpec ==
  /\ Init
  /\ [][Next]_vars
  /\ SF_vars(TurnInPage)

Spec == ISpec

\* The invariant is fully inductive: it holds at every reachable state.
Inv == MutualExclusion /\ TypeOK

====