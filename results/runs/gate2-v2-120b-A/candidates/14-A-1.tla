---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, MaxNat, Nat

\* ----------------------------------------------------------------------
\* State variables (inherited from Boulanger)
\* ----------------------------------------------------------------------
VARIABLES
    pc,         \* program counter for each process
    ticket,     \* ticket number for each process
    next        \* next ticket number to assign

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1..N

\* ----------------------------------------------------------------------
\* Types and type correctness predicate
\* ----------------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> {"idle", "request", "cs", "exit"}]
    /\ ticket \in [Proc -> Nat]
    /\ next \in Nat

\* ----------------------------------------------------------------------
\* Initial state (inherits from Boulanger, restricted to Nat)
\* ----------------------------------------------------------------------
Init ==
    /\ pc = [i \in Proc |-> "idle"]
    /\ ticket = [i \in Proc |-> 0]
    /\ next = 1

\* ----------------------------------------------------------------------
\* Actions (inherit the Boulanger algorithm)
\* ----------------------------------------------------------------------
Request(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "request"]
    /\ ticket' = [ticket EXCEPT ![i] = next]
    /\ next' = IF next < MaxNat THEN next + 1 ELSE 1
    /\ UNCHANGED pc

Enter(i) ==
    /\ pc[i] = "request"
    /\ \A j \in Proc : (j # i) => (ticket[i] < ticket[j] \/ (ticket[i] = ticket[j] /\ i < j))
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<ticket, next>>

Exit(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED <<ticket, next>>

Next ==
    \/ \E i \in Proc : Request(i)
    \/ \E i \in Proc : Enter(i)
    \/ \E i \in Proc : Exit(i)

\* ----------------------------------------------------------------------
\* Full specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<pc, ticket, next>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
MutualExclusion ==
    \A i, j \in Proc : i # j => ~(pc[i] = "cs" /\ pc[j] = "cs")

Inv ==
    /\ MutualExclusion
    /\ TypeOK
    /\ \A i \in Proc : ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\* State constraint to keep ticket numbers within bounds (prunes illegal states)
\* ----------------------------------------------------------------------
StateConstraint ==
    \A i \in Proc : ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\* Specification name expected by the .cfg file
\* ----------------------------------------------------------------------
SpecName == Spec

\* ----------------------------------------------------------------------
\* Theorems (optional, just to expose the identifiers)
\* ----------------------------------------------------------------------
THEOREM SpecIsSpec == Spec
THEOREM MutualExclusionInv == MutualExclusion
THEOREM TypeOKInv == TypeOK
THEOREM FullInv == Inv

====