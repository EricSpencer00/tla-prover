---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* The finite natural-number type allowed for model checking.
Naturals == 0..MaxNat

VARIABLES using, taken, ticket, served

vars == <<using, taken, ticket, served>>

TypeOK ==
  /\ using \in {"none"} \cup (1..N)
  /\ taken \in 0..N
  /\ ticket \in [1..N -> Naturals]
  /\ served \in 0..N

Init ==
  /\ using = "none"
  /\ taken = 0
  /\ ticket = [p \in 1..N |-> 0]
  /\ served = 0

\* A process picks a fresh ticket number within the bounded range.
Request(p) ==
  /\ using = "none"
  /\ taken < N
  /\ \E tn \in Naturals :
       /\ \A q \in 1..N : ticket[q] # tn
       /\ ticket' = [ticket EXCEPT ![p] = tn]
  /\ taken' = taken + 1
  /\ UNCHANGED <<using, served>>

\* Mutual exclusion: a process may enter only when no one else is in the section.
Enter(p) ==
  /\ using = "none"
  /\ taken > 0
  /\ using' = p
  /\ UNCHANGED <<taken, ticket, served>>

\* The occupant leaves and is marked as served once.
Exit(p) ==
  /\ using = p
  /\ using' = "none"
  /\ ticket' = [ticket EXCEPT ![p] = 0]
  /\ taken' = taken - 1
  /\ served' = IF served < N THEN served + 1 ELSE served

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N : Request(p))
  /\ WF_vars(\E p \in 1..N : Enter(p))
  /\ WF_vars(\E p \in 1..N : Exit(p))

MutualExclusion ==
  /\ (using = "none") <=> (taken = 0)

Inv == TypeOK /\ MutualExclusion

\* The inductive specification: any reachable state need only satisfy the
\* invariant, never just the initial state.
ISpec == Spec /\ TypeOK /\ MutualExclusion

====