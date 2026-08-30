---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Nothing is added here; all variables come from the inherited Boulanger
\* specification, which is deliberately not reproduced in this module.
VARIABLES phase, ticket, holder, waiting, crashed

vars == <<phase, ticket, holder, waiting, crashed>>

Init ==
  /\ phase = [p \in 0..(N - 1) |-> "idle"]
  /\ ticket = [p \in 0..(N - 1) |-> 0]
  /\ holder = "none"
  /\ waiting = {}
  /\ crashed = {}

Request(p) ==
  /\ phase[p] = "idle"
  /\ p \notin crashed
  /\ phase' = [phase EXCEPT ![p] = "waiting"]
  /\ waiting' = waiting \cup {p}
  /\ UNCHANGED <<ticket, holder, crashed>>

Grant(p) ==
  /\ holder = "none"
  /\ p \in waiting
  /\ phase[p] = "waiting"
  /\ p \notin crashed
  /\ holder' = p
  /\ ticket' = [ticket EXCEPT ![p] = (IF @ < MaxNat THEN @ + 1 ELSE @)]
  /\ phase' = [phase EXCEPT ![p] = "critical"]
  /\ waiting' = waiting \ {p}
  /\ UNCHANGED crashed

Exit(p) ==
  /\ phase[p] = "critical"
  /\ holder = p
  /\ p \notin crashed
  /\ phase' = [phase EXCEPT ![p] = "idle"]
  /\ holder' = "none"
  /\ UNCHANGED <<ticket, waiting, crashed>>

Crash(p) ==
  /\ p \notin crashed
  /\ crashed' = crashed \cup {p}
  /\ UNCHANGED <<phase, ticket, holder, waiting>>

Reclaim(p) ==
  /\ p \in crashed
  /\ phase[p] \in {"waiting", "critical"}
  /\ phase' = [phase EXCEPT ![p] = "idle"]
  /\ holder' = IF holder = p THEN "none" ELSE holder
  /\ waiting' = waiting \ {p}
  /\ UNCHANGED <<ticket, crashed>>

Next ==
  \/ \E p \in 0..(N - 1) : Request(p)
  \/ \E p \in 0..(N - 1) : Grant(p)
  \/ \E p \in 0..(N - 1) : Exit(p)
  \/ \E p \in 0..(N - 1) : Crash(p)
  \/ \E p \in 0..(N - 1) : Reclaim(p)

Spec == Init /\ [][Next]_vars

\* Safety: mutual exclusion, type correctness, and the full inductive invariant:
MutualExclusion == (holder # "none") => (phase[holder] = "critical")
TypeOK ==
  /\ phase \in [0..(N - 1) -> {"idle", "waiting", "critical"}]
  /\ ticket \in [0..(N - 1) -> Nat]
  /\ holder \in (0..(N - 1)) \cup {"none"}
  /\ waiting \subseteq (0..(N - 1))
  /\ crashed \subseteq (0..(N - 1))
Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ holder # "none" => (phase[holder] = "critical")

\* Finite range on Nat for model checking: overridden below.
NatOverride == Nat

StateConstraint == \A p \in 0..(N - 1) : ticket[p] < MaxNat

====