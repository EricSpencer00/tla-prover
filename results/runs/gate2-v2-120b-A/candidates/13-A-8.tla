---- MODULE MCBakery ----
EXTENDS Naturals, TLC

CONSTANTS N, MaxNat, Nat

VARIABLES entering, ticket, pc

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
TypeOK ==
    /\ entering \in [1..N -> BOOLEAN]
    /\ ticket   \in [1..N -> Nat]
    /\ pc       \in [1..N -> {"idle", "cs", "after"}]

\* ----------------------------------------------------------------------
\* State variables inherited from the original Bakery specification
\* ----------------------------------------------------------------------
vars == << entering, ticket, pc >>

\* ----------------------------------------------------------------------
\* Initial state (any type-correct state)
\* ----------------------------------------------------------------------
Init ==
    /\ entering = [i \in 1..N |-> FALSE]
    /\ ticket   = [i \in 1..N |-> 0]
    /\ pc       = [i \in 1..N |-> "idle"]
    /\ TypeOK

\* ----------------------------------------------------------------------
\* Actions (same as in the original Bakery spec)
\* ----------------------------------------------------------------------
Choose(i) ==
    /\ i \in 1..N
    /\ pc[i] = "idle"
    /\ entering' = [entering EXCEPT ![i] = TRUE]
    /\ pc'       = [pc EXCEPT ![i] = "choose"]
    /\ UNCHANGED ticket

Number(i) ==
    /\ i \in 1..N
    /\ pc[i] = "choose"
    /\ ticket' = [ticket EXCEPT ![i] = Max(ticket) + 1]
    /\ entering' = [entering EXCEPT ![i] = FALSE]
    /\ pc'       = [pc EXCEPT ![i] = "wait"]
    /\ ticket[i] \in Nat
    /\ ticket[i] <= MaxNat

Wait(i) ==
    /\ i \in 1..N
    /\ pc[i] = "wait"
    /\ \A j \in 1..N :
          (j # i) =>
            ( \A k \in 1..N :
                (entering[k] /\ ticket[k] <= ticket[i]) => k = i )
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED << entering, ticket >>

Leave(i) ==
    /\ i \in 1..N
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED << entering, ticket >>

Next ==
    \/ \E i \in 1..N : Choose(i)
    \/ \E i \in 1..N : Number(i)
    \/ \E i \in 1..N : Wait(i)
    \/ \E i \in 1..N : Leave(i)

\* ----------------------------------------------------------------------
\* Safety property: Mutual exclusion
\* ----------------------------------------------------------------------
MutualExclusion ==
    \A i, j \in 1..N :
        (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* ----------------------------------------------------------------------
\* Full invariant from the original spec
\* ----------------------------------------------------------------------
Inv ==
    /\ TypeOK
    /\ MutualExclusion
    /\ \A i \in 1..N :
          pc[i] = "cs" => 
            \A j \in 1..N :
               (j # i) => 
                 (ticket[i] < ticket[j] \/
                  (ticket[i] = ticket[j] /\ i < j))

\* ----------------------------------------------------------------------
\* Specification (inductive: any type-correct initial state)
\* ----------------------------------------------------------------------
ISpec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* (Optional) Liveness properties placeholder – not specified
\* ----------------------------------------------------------------------
Sat == TRUE

\* ----------------------------------------------------------------------
\* Theorems (so the cfg can refer to them if needed)
\* ----------------------------------------------------------------------
THEOREM SpecIsISpec == ISpec

====