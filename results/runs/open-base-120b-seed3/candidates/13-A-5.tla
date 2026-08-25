---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, MaxNat

\* Finite version of the natural numbers used in the model
NatOverride == 0..MaxNat

VARIABLES flag, ticket, pc

\* Set of process identifiers
ProcSet == 1..N

\* Tuple of all state variables (used for stuttering)
vars == <<flag, ticket, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
    /\ flag \in [ProcSet -> BOOLEAN]
    /\ ticket \in [ProcSet -> NatOverride]
    /\ pc \in [ProcSet -> {"idle", "waiting", "cs"}]

\* ----------------------------------------------------------------------
\* Initial state (same as the original Bakery spec, but with finite Nat)
Init ==
    /\ flag = [i \in ProcSet |-> FALSE]
    /\ ticket = [i \in ProcSet |-> 0]
    /\ pc = [i \in ProcSet |-> "idle"]
    /\ TypeOK

\* ----------------------------------------------------------------------
\* Helper: maximum ticket among all processes
MaxTicket == Max({ ticket[i] : i \in ProcSet })

\* ----------------------------------------------------------------------
\* Actions for a single process i
Enter(i) ==
    /\ i \in ProcSet
    /\ pc[i] = "idle"
    /\ flag' = [flag EXCEPT ![i] = TRUE]
    /\ ticket' = [ticket EXCEPT ![i] = MaxTicket + 1]
    /\ pc' = [pc EXCEPT ![i] = "waiting"]
    /\ UNCHANGED << >>

Wait(i) ==
    /\ i \in ProcSet
    /\ pc[i] = "waiting"
    /\ \A j \in ProcSet :
          ( ~ flag[j] )
          \/ ( ticket[i] < ticket[j] )
          \/ ( ticket[i] = ticket[j] /\ i < j )
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED << flag, ticket >>

Exit(i) ==
    /\ i \in ProcSet
    /\ pc[i] = "cs"
    /\ flag' = [flag EXCEPT ![i] = FALSE]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED << >>

Next ==
    \/ \E i \in ProcSet : Enter(i)
    \/ \E i \in ProcSet : Wait(i)
    \/ \E i \in ProcSet : Exit(i)

\* ----------------------------------------------------------------------
\* Safety invariants
MutualExclusion ==
    \A i, j \in ProcSet :
        (pc[i] = "cs" /\ pc[j] = "cs") => i = j

Inv == TypeOK /\ MutualExclusion

\* ----------------------------------------------------------------------
\* Inductive specification (used by the .cfg)
ISpec == Init /\ [][Next]_vars

=============================================================================