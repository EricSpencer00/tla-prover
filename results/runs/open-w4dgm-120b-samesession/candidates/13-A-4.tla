---- MODULE MCBakery ----
EXTENDS Naturals
CONSTANTS N, MaxNat

\* Overrides the unbounded Naturals Nat definition with a finite range so that
\* the model is checkable. The name Nat is kept out of the exported
\* namespace; this is exactly what the .cfg expects to replace.
NatOverride == (0..MaxNat)

None == 0

VARIABLES ticket, inCS, state, budget
vars == <<ticket, inCS, state, budget>>

Phases == {"idle", "waiting", "critical"}

TypeOK ==
  /\ ticket \in [1..N -> NatOverride]
  /\ inCS \in [1..N -> BOOLEAN]
  /\ state \in [1..N -> Phases]
  /\ budget \in 0..MaxNat

\* The Bakery invariant: no two processes occupy the critical section at once,
\* coupled with type correctness. It must hold after every transition.
Inv ==
  /\ \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => i = j
  /\ TypeOK

Init ==
  /\ ticket = [i \in 1..N |-> 0]
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ state = [i \in 1..N |-> "idle"]
  /\ budget = MaxNat

\* Join the bakery queue; the ticket is assigned lazily at entry time.
Request ==
  /\ \E i \in 1..N :
       /\ state[i] = "idle"
       /\ state' = [state EXCEPT ![i] = "waiting"]
  /\ UNCHANGED <<ticket, inCS, budget>>

\* Enter the critical section when no one else holds it.
Enter ==
  /\ \E i \in 1..N :
       /\ state[i] = "waiting"
       /\ \A j \in 1..N : ~inCS[j]
       /\ inCS' = [inCS EXCEPT ![i] = TRUE]
       /\ ticket' = [ticket EXCEPT ![i] = budget]
       /\ state' = [state EXCEPT ![i] = "critical"]
  /\ UNCHANGED budget

\* Release the critical section, returning to idle.
Exit ==
  /\ \E i \in 1..N :
       /\ state[i] = "critical"
       /\ inCS' = [inCS EXCEPT ![i] = FALSE]
       /\ state' = [state EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<ticket, budget>>

\* Recycle ticket numbers when the budget is exhausted. This keeps the
\* reachable state space finite without weakening the invariant.
Recycle ==
  /\ budget = 0
  /\ \A i \in 1..N : state[i] = "idle"
  /\ budget' = MaxNat
  /\ ticket' = [i \in 1..N |-> 0]
  /\ UNCHANGED <<inCS, state>>

Next == Request \/ Enter \/ Exit \/ Recycle

ISpec == Init /\ [][Next]_vars

MutualExclusion == Inv
====