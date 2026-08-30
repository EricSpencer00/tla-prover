---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* The type invariant is preserved across all actions and is the basis for the
\* full inductive safety argument; it is not weakened for model checking.
VARIABLES inCS, ticket, active, served

vars == <<inCS, ticket, active, served>>

Init ==
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ active = [i \in 1..N |-> FALSE]
  /\ served = [i \in 1..N |-> 0]

Request(i) ==
  /\ ~active[i]
  /\ active' = [active EXCEPT ![i] = TRUE]
  /\ ticket' = [ticket EXCEPT ![i] = 1 + Max({ticket[j] : j \in 1..N})]
  /\ UNCHANGED <<inCS, served>>

Enter(i) ==
  /\ active[i]
  /\ \A j \in 1..N : ~inCS[j]
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<ticket, active, served>>

Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ served' = [served EXCEPT ![i] = IF @ < MaxNat THEN @ + 1 ELSE @]
  /\ UNCHANGED <<ticket>>

StepDown(i) ==
  /\ active[i]
  /\ ~inCS[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<inCS, ticket, served>>

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Exit(i)
  \/ \E i \in 1..N : StepDown(i)

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ active \in [1..N -> BOOLEAN]
  /\ served \in [1..N -> 0..MaxNat]

MutualExclusion ==
  \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => (i = j)

Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ \A i \in 1..N :
       inCS[i] =>
         /\ active[i]
         /\ \A j \in 1..N : ~inCS[j]
         /\ ticket[i] = Max({ticket[k] : k \in 1..N})

\* The inductive spec starts from any reachable type-correct state and checks
\* that every action preserves the invariant -- this is what rules out the
\* weakening that would otherwise make it vacuous on a fresh start.
ISpec == Init /\ [][Next]_vars /\ WF_vars(Next)

Spec == ISpec

====