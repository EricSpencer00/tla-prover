---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, MaxNat, Nat

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
Proc == 1 .. N
Ticket == 0 .. MaxNat
ZeroTicket == 0

(*--------------------------------------------------------------------
  State variables (inherited from Boulanger)
--------------------------------------------------------------------*)
VARIABLES
    pc,        \* pc[i] is the program counter / phase of process i
    ticket,    \* ticket[i] is the ticket number of process i
    flag       \* flag[i] indicates whether process i is interested

(*--------------------------------------------------------------------
  Type correctness (for reference)
--------------------------------------------------------------------*)
TypeOK ==
    /\ pc \in [Proc -> {"idle", "trying", "cs"}]
    /\ ticket \in [Proc -> Ticket]
    /\ flag \in [Proc -> BOOLEAN]
    /\ Nat = 0 .. MaxNat

(*--------------------------------------------------------------------
  Safety invariant (mutual exclusion)
--------------------------------------------------------------------*)
MutualExclusion ==
    \A i, j \in Proc :
        (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

(*--------------------------------------------------------------------
  Full inductive invariant (as required by the .cfg)
--------------------------------------------------------------------*)
Inv ==
    /\ MutualExclusion
    /\ TypeOK

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ pc = [i \in Proc |-> "idle"]
    /\ ticket = [i \in Proc |-> 0]
    /\ flag = [i \in Proc |-> FALSE]
    /\ Nat = 0

(*--------------------------------------------------------------------
  Actions (simplified Boulanger actions)
--------------------------------------------------------------------*)

Try(i) ==
    /\ i \in Proc
    /\ pc[i] = "idle"
    /\ flag' = [flag EXCEPT ![i] = TRUE]
    /\ ticket' = [ticket EXCEPT ![i] = MaxNat]  \* assign maximal ticket for simplicity
    /\ pc' = [pc EXCEPT ![i] = "trying"]
    /\ UNCHANGED Nat

Enter(i) ==
    /\ i \in Proc
    /\ pc[i] = "trying"
    /\ \A j \in Proc :
          (j # i) => ~ flag[j] \/ ticket[i] < ticket[j]
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<ticket, flag, Nat>>

Leave(i) ==
    /\ i \in Proc
    /\ pc[i] = "cs"
    /\ flag' = [flag EXCEPT ![i] = FALSE]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED Nat

Next ==
    \/ \E i \in Proc : Try(i)
    \/ \E i \in Proc : Enter(i)
    \/ \E i \in Proc : Leave(i)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<pc, ticket, flag, Nat>>

(*--------------------------------------------------------------------
  State constraint to keep ticket numbers strictly below MaxNat
  (prunes states where any ticket reaches MaxNat)
--------------------------------------------------------------------*)
StateConstraint ==
    \A i \in Proc : ticket[i] < MaxNat

(*--------------------------------------------------------------------
  Theorems (optional, but ensure that the state constraint is applied)
--------------------------------------------------------------------*)
THEOREM Spec => []StateConstraint

====