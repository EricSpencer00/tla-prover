---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANT N \* Number of processes (set in the .cfg)
CONSTANT MaxNat \* Upper bound for finite natural numbers (set in the .cfg)

(*--------------------------------------------------------------------
  Derived constant to override the infinite Nat set with a finite range.
--------------------------------------------------------------------*)
Nat == 0 .. MaxNat

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
Proc == 1 .. N

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES pc, ticket, nextTicket

(*--------------------------------------------------------------------
  Type definitions (for clarity, not used directly in the spec)
--------------------------------------------------------------------*)
PCVals == {"idle", "waiting", "cs", "exit"}

(*--------------------------------------------------------------------
  Initial state (inherits from Boulanger, adapted to finite Nat)
--------------------------------------------------------------------*)
Init ==
  /\ pc = [i \in Proc |-> "idle"]
  /\ ticket = [i \in Proc |-> 0]
  /\ nextTicket = 0

(*--------------------------------------------------------------------
  Actions (inherits from Boulanger)
--------------------------------------------------------------------*)
Request(i) ==
  /\ i \in Proc
  /\ pc[i] = "idle"
  /\ LET t == nextTicket IN
       /\ ticket' = [ticket EXCEPT ![i] = t]
       /\ nextTicket' = t + 1
       /\ pc' = [pc EXCEPT ![i] = "waiting"]
  /\ UNCHANGED << >>

Enter(i) ==
  /\ i \in Proc
  /\ pc[i] = "waiting"
  /\ \A j \in Proc :
        (j # i) => (pc[j] # "cs" \/ ticket[i] < ticket[j]
                    \/ (ticket[i] = ticket[j] /\ i < j))
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << ticket, nextTicket >>

Exit(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ UNCHANGED << ticket, nextTicket >>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
  \/ \E i \in Proc : Request(i)
  \/ \E i \in Proc : Enter(i)
  \/ \E i \in Proc : Exit(i)

(*--------------------------------------------------------------------
  State constraint to keep ticket numbers within bounds.
--------------------------------------------------------------------*)
StateConstraint ==
  /\ \A i \in Proc : ticket[i] < MaxNat
  /\ nextTicket < MaxNat

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<pc, ticket, nextTicket>>
        /\ StateConstraint

(*--------------------------------------------------------------------
  Safety properties (invariants)
--------------------------------------------------------------------*)
MutualExclusion ==
  \A i, j \in Proc : i # j => ~(pc[i] = "cs" /\ pc[j] = "cs")

TypeOK ==
  /\ pc \in [Proc -> PCVals]
  /\ ticket \in [Proc -> Nat]
  /\ nextTicket \in Nat

Inv ==
  /\ MutualExclusion
  /\ TypeOK

=============================================================================