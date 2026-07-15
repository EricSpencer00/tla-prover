---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

\* The finite range of natural numbers used for model checking
Nat == 0 .. MaxNat

VARIABLES pc, ticket

\* ----------------------------------------------------------------------
\* State definitions
\* ----------------------------------------------------------------------
\* pc[p] : program counter of process p
\* ticket[p] : ticket number of process p (must stay within Nat)
\* ----------------------------------------------------------------------
Nset == 1 .. N

ProcSet == Nset

\* Initial state
Init ==
    /\ pc = [p \in ProcSet |-> "idle"]
    /\ ticket = [p \in ProcSet |-> 0]

\* ----------------------------------------------------------------------
\* Actions (imports from the original Boulanger algorithm, adapted to Nat)
\* ----------------------------------------------------------------------
Request(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ ticket' = [ticket EXCEPT ![p] = 
        ( IF \E q \in ProcSet: ticket[q] # 0 
          THEN 1 + Max({ ticket[q] : q \in ProcSet })
          ELSE 1 )]
    /\ \A p \in ProcSet: ticket[p] \in Nat

Wait(p) ==
    /\ pc[p] = "wait"
    /\ \A q \in ProcSet:
          ( ( ticket[q] # 0 ) => 
              ( ticket[p] > ticket[q] \/ ( ticket[p] = ticket[q] /\ p > q ) ) )
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED ticket

Release(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ ticket' = [ticket EXCEPT ![p] = 0]

Next ==
    \/ \E p \in ProcSet: Request(p)
    \/ \E p \in ProcSet: Wait(p)
    \/ \E p \in ProcSet: Release(p)

\* ----------------------------------------------------------------------
\* Full specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, ticket>>

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
\* Mutual exclusion: at most one process can be in the critical section
MutualExclusion ==
    \A p, q \in ProcSet :
        ( p # q ) => ~( pc[p] = "cs" /\ pc[q] = "cs" )

\* Type correctness
TypeOK ==
    /\ pc \in [ProcSet -> {"idle", "wait", "cs"}]
    /\ ticket \in [ProcSet -> Nat]

\* Full inductive invariant (here taken as the conjunction of the two
\* essential safety conditions)
Inv == MutualExclusion /\ TypeOK

\* ----------------------------------------------------------------------
\* State constraint to keep all tickets strictly below MaxNat
\* ----------------------------------------------------------------------
StateConstraint ==
    \A p \in ProcSet: ticket[p] < MaxNat

\* ----------------------------------------------------------------------
\* Theorem to help TLC (optional, does not affect the model)
\* ----------------------------------------------------------------------
THEOREM Spec => []StateConstraint

====