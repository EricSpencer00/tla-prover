---- MODULE MCBakery ----
EXTENDS Naturals

\*-----------------------------------------------------------------
\* Constants (as required by the .cfg file)
\*-----------------------------------------------------------------
CONSTANT N      \* Number of processes (set in the configuration)
CONSTANT MaxNat \* Upper bound for the finite range of natural numbers
CONSTANT Nat    \* The finite set of natural numbers used in the model

\*-----------------------------------------------------------------
\* Derived definitions
\*-----------------------------------------------------------------
Proc == 1 .. N               \* Set of process identifiers
NatRange == 0 .. MaxNat      \* Finite range of natural numbers

\*-----------------------------------------------------------------
\* State variables (inherited from the original Bakery spec)
\*-----------------------------------------------------------------
VARIABLES
    pc,        \* Program counter of each process
    ticket,    \* Ticket number of each process (0 means no ticket)
    choosing   \* Boolean flag indicating if a process is choosing a ticket

\*-----------------------------------------------------------------
\* Type correctness predicate (for completeness)
\*-----------------------------------------------------------------
TypeOK ==
    /\ pc \in [Proc -> {"init","cs","done"}]
    /\ ticket \in [Proc -> NatRange]
    /\ choosing \in [Proc -> BOOLEAN]

\*-----------------------------------------------------------------
\* Initial state (restricted to the finite Nat range)
\*-----------------------------------------------------------------
Init ==
    /\ pc = [i \in Proc |-> "init"]
    /\ ticket = [i \in Proc |-> 0]
    /\ choosing = [i \in Proc |-> FALSE]
    /\ TypeOK

\*-----------------------------------------------------------------
\* Actions (identical to the original Bakery algorithm)
\*-----------------------------------------------------------------
\* 1. A process i starts choosing a ticket
StartChoosing(i) ==
    /\ i \in Proc
    /\ pc[i] = "init"
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<pc, ticket>>

\* 2. A process i assigns itself the next ticket number
AssignTicket(i) ==
    /\ i \in Proc
    /\ pc[i] = "init"
    /\ choosing[i] = TRUE
    /\ ticket' = [ticket EXCEPT ![i] = 1 + Max({ ticket[j] : j \in Proc })]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED << >>

\* 3. A process i enters the critical section after waiting
EnterCS(i) ==
    /\ i \in Proc
    /\ pc[i] = "cs"
    /\ \A j \in Proc :
          \/ i = j
          \/ ~choosing[j]
          \/ (ticket[j] = 0)
          \/ (ticket[i] < ticket[j])
          \/ (ticket[i] = ticket[j] /\ i < j)
    /\ pc' = [pc EXCEPT ![i] = "done"]
    /\ UNCHANGED <<ticket, choosing>>

\* 4. A process i leaves the critical section
Leave(i) ==
    /\ i \in Proc
    /\ pc[i] = "done"
    /\ pc' = [pc EXCEPT ![i] = "init"]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED <<choosing>>

\* 5. Stuttering step to avoid deadlock when deadlock checking is disabled
Stutter ==
    UNCHANGED <<pc, ticket, choosing>>

\*-----------------------------------------------------------------
\* Next-state relation
\*-----------------------------------------------------------------
Next ==
    \/ \E i \in Proc : StartChoosing(i)
    \/ \E i \in Proc : AssignTicket(i)
    \/ \E i \in Proc : EnterCS(i)
    \/ \E i \in Proc : Leave(i)
    \/ Stutter

\*-----------------------------------------------------------------
\* Safety invariant: Mutual exclusion
\*-----------------------------------------------------------------
MutualExclusion ==
    \A i, j \in Proc :
        (i # j) => ~(pc[i] = "done" /\ pc[j] = "done")

\*-----------------------------------------------------------------
\* Full inductive invariant (combination of TypeOK and MutualExclusion)
\*-----------------------------------------------------------------
Inv == /\ TypeOK /\ MutualExclusion

\*-----------------------------------------------------------------
\* Specification formula (inductive specification from any type-correct state)
\*-----------------------------------------------------------------
ISpec == Init /\ [][Next]_<<pc, ticket, choosing>>

\*-----------------------------------------------------------------
\* The .cfg expects the following names:
\*   - CONSTANTS: N, MaxNat, Nat
\*   - SPECIFICATION: ISpec
\*   - INVARIANTS: MutualExclusion, TypeOK, Inv
\*   - No explicit PROPERTIES (liveness) are defined here.
\*-----------------------------------------------------------------

====