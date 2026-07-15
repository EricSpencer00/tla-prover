---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANT N
CONSTANT MaxNat
CONSTANT Nat

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
Proc == 1..N

(*--------------------------------------------------------------------
  State variables (same as in the original Boulanger spec)
--------------------------------------------------------------------*)
VARIABLES
    pc,        \* program counter of each process
    flag,      \* flag[i] = TRUE iff process i is interested
    ticket,    \* ticket[i] is the ticket number of process i (Nat)
    nextTicket \* the next ticket number to be assigned (Nat)

(*--------------------------------------------------------------------
  Type correctness (helps readability)
--------------------------------------------------------------------*)
TypeOK ==
    /\ pc \in [Proc -> {"idle", "request", "wait", "cs", "exit"}]
    /\ flag \in [Proc -> BOOLEAN]
    /\ ticket \in [Proc -> Nat]
    /\ nextTicket \in Nat

(*--------------------------------------------------------------------
  Initial state (same as Boulanger, but Nat is finite)
--------------------------------------------------------------------*)
Init ==
    /\ pc = [i \in Proc |-> "idle"]
    /\ flag = [i \in Proc |-> FALSE]
    /\ ticket = [i \in Proc |-> 0]
    /\ nextTicket = 0
    /\ TypeOK

(*--------------------------------------------------------------------
  Actions (identical to Boulanger)
--------------------------------------------------------------------*)
Request(i) ==
    /\ i \in Proc
    /\ pc[i] = "idle"
    /\ flag' = [flag EXCEPT ![i] = TRUE]
    /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
    /\ nextTicket' = nextTicket + 1
    /\ pc' = [pc EXCEPT ![i] = "request"]
    /\ UNCHANGED << >>

Wait(i) ==
    /\ i \in Proc
    /\ pc[i] = "request"
    /\ \A j \in Proc :
          (j # i) => ~flag[j] \/ ticket[i] < ticket[j] \/ (ticket[i] = ticket[j] /\ i < j)
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED << flag, ticket, nextTicket >>

Exit(i) ==
    /\ i \in Proc
    /\ pc[i] = "cs"
    /\ flag' = [flag EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED << ticket, nextTicket >>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ \E i \in Proc : Request(i)
    \/ \E i \in Proc : Wait(i)
    \/ \E i \in Proc : Exit(i)

(*--------------------------------------------------------------------
  Full specification (behavioral)
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_ <<pc, flag, ticket, nextTicket>>

(*--------------------------------------------------------------------
  Safety properties
--------------------------------------------------------------------*)
MutualExclusion ==
    \A i, j \in Proc :
        (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Inv ==
    /\ MutualExclusion
    /\ TypeOK
    /\ \A i \in Proc : ticket[i] < MaxNat

(*--------------------------------------------------------------------
  State constraint to prune states where any ticket reaches MaxNat
--------------------------------------------------------------------*)
StateConstraint ==
    \A i \in Proc : ticket[i] < MaxNat

(*--------------------------------------------------------------------
  Theorem (optional, shows that Spec implies the invariant)
--------------------------------------------------------------------*)
THEOREM Spec => []Inv

====