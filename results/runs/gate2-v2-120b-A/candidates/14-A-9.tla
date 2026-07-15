---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANT N, MaxNat, Nat

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
ProcSet == 1 .. N

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    pc,          \* program counter / phase of each process
    ticket,      \* ticket number for each process
    choosing,    \* flag indicating a process is choosing a ticket
    lock,        \* the lock holder (0 means unlocked)
    NatVar       \* a placeholder variable to illustrate the overridden Nat set

(*--------------------------------------------------------------------
  Type definitions (used for readability)
--------------------------------------------------------------------*)
PCVals == {"Idle", "Enter", "CS", "Exit"}

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ pc = [i \in ProcSet |-> "Idle"]
    /\ ticket = [i \in ProcSet |-> 0]
    /\ choosing = [i \in ProcSet |-> FALSE]
    /\ lock = 0
    /\ NatVar \in Nat
    /\ \A i \in ProcSet: ticket[i] < MaxNat

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
Enter(i) ==
    /\ pc[i] = "Idle"
    /\ choosing[i] = FALSE
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<pc, ticket, lock, NatVar>>
    /\ pc' = [pc EXCEPT ![i] = "Enter"]
    /\ ticket' = [ticket EXCEPT ![i] = MaxNat] \* assign a ticket within bound
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]

CS(i) ==
    /\ pc[i] = "Enter"
    /\ lock = 0
    /\ lock' = i
    /\ pc' = [pc EXCEPT ![i] = "CS"]
    /\ UNCHANGED <<ticket, choosing, NatVar>>

Exit(i) ==
    /\ pc[i] = "CS"
    /\ lock = i
    /\ lock' = 0
    /\ pc' = [pc EXCEPT ![i] = "Exit"]
    /\ UNCHANGED <<ticket, choosing, NatVar>>

Idle(i) ==
    /\ pc[i] = "Exit"
    /\ pc' = [pc EXCEPT ![i] = "Idle"]
    /\ UNCHANGED <<ticket, choosing, lock, NatVar>>

Next ==
    \E i \in ProcSet: \/ Enter(i) \/ CS(i) \/ Exit(i) \/ Idle(i)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<pc, ticket, choosing, lock, NatVar>>

(*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*)
MutualExclusion ==
    /\ \A i, j \in ProcSet: i # j => ~(pc[i] = "CS" /\ pc[j] = "CS")
    /\ (lock # 0) => \E i \in ProcSet: lock = i /\ pc[i] = "CS"

TypeOK ==
    /\ pc \in [ProcSet -> PCVals]
    /\ ticket \in [ProcSet -> Nat]
    /\ \A i \in ProcSet: ticket[i] < MaxNat
    /\ choosing \in [ProcSet -> BOOLEAN]
    /\ lock \in ProcSet \cup {0}
    /\ NatVar \in Nat

Inv ==
    /\ MutualExclusion
    /\ TypeOK

=============================================================================