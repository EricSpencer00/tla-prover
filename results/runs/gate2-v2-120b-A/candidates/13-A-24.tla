---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\*-----------------------------------------------------------------
\* Constants (provided by the .cfg)
\*-----------------------------------------------------------------
CONSTANT N          \* number of processes
CONSTANT MaxNat    \* maximum value of the overridden natural numbers
CONSTANT Nat       \* finite set representing natural numbers 0..MaxNat

\*-----------------------------------------------------------------
\* Derived constants
\*-----------------------------------------------------------------
ProcSet == 1 .. N

\*-----------------------------------------------------------------
\* State variables (inherited from the original Bakery specification)
\*-----------------------------------------------------------------
VARIABLES
    pc,          \* program counter, a map ProcSet -> {"idle","request","wait","cs","exit"}
    ticket,      \* ticket numbers, a map ProcSet -> Nat
    choosing     \* choosing flag, a map ProcSet -> BOOLEAN

\*-----------------------------------------------------------------
\* Type correctness predicate
\*-----------------------------------------------------------------
TypeOK ==
    /\ pc \in [ProcSet -> {"idle","request","wait","cs","exit"}]
    /\ ticket \in [ProcSet -> Nat]
    /\ choosing \in [ProcSet -> BOOLEAN]

\*-----------------------------------------------------------------
\* Initial state (same as original Bakery, with tickets in Nat)
\*-----------------------------------------------------------------
Init ==
    /\ pc = [i \in ProcSet |-> "idle"]
    /\ ticket = [i \in ProcSet |-> 0]
    /\ choosing = [i \in ProcSet |-> FALSE]
    /\ TypeOK

\*-----------------------------------------------------------------
\* Helper definitions used by actions
\*-----------------------------------------------------------------
GreaterThan(i, j) ==
    /\ ticket[i] > ticket[j]
    \/ /\ ticket[i] = ticket[j]
       /\ i > j

\*-----------------------------------------------------------------
\* Actions (exactly the same as in the original Bakery spec)
\*-----------------------------------------------------------------
Request(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "request"]
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED ticket

SetTicket(i) ==
    /\ pc[i] = "request"
    /\ ticket' = [ticket EXCEPT ![i] = 1 + Max({ticket[j] : j \in ProcSet})]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ UNCHANGED pc

Wait(i) ==
    /\ pc[i] = "wait"
    /\ \A j \in ProcSet :
          (j # i) => ~choosing[j] /\ (ticket[j] = 0 \/ ~GreaterThan(j, i))
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<ticket, choosing>>

Exit(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED choosing

\*-----------------------------------------------------------------
\* Next-state relation (any process may take any enabled step)
\*-----------------------------------------------------------------
Next ==
    \E i \in ProcSet :
        \/ Request(i)
        \/ SetTicket(i)
        \/ Wait(i)
        \/ Exit(i)

\*-----------------------------------------------------------------
\* Specification (inductive: start from any state satisfying Init)
\*-----------------------------------------------------------------
ISpec == Init /\ [][Next]_<<pc, ticket, choosing>>

\*-----------------------------------------------------------------
\* Safety invariants
\*-----------------------------------------------------------------
MutualExclusion ==
    \A i, j \in ProcSet :
        (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

Inv == MutualExclusion /\ TypeOK

\*-----------------------------------------------------------------
\* Liveness properties (none specified)
\*-----------------------------------------------------------------
Skip

====