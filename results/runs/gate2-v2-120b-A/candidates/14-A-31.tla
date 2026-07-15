---- MODULE MCBoulanger ----
EXTENDS Naturals, TLC

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANT N          \* number of processes (set in the .cfg)
CONSTANT MaxNat    \* finite upper bound for natural numbers (set in the .cfg)

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
Nat == 0 .. MaxNat
Proc == 1 .. N

(*-----------------------------------------------------------------
  State variables (inherited from Boulanger)
-----------------------------------------------------------------*)
VARIABLES pc,   \* program counters: "idle", "wait", "cs", "exit"
          ticket \* ticket numbers for each process

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
PCSet == {"idle", "wait", "cs", "exit"}

(*-----------------------------------------------------------------
  Initial predicate
-----------------------------------------------------------------*)
Init ==
  /\ pc = [i \in Proc |-> "idle"]
  /\ ticket = [i \in Proc |-> 0]
  /\ \A i \in Proc: ticket[i] \in Nat

(*-----------------------------------------------------------------
  Actions (inherit from Boulanger)
-----------------------------------------------------------------*)
Acquire(i) ==
  /\ i \in Proc
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ ticket' = [ticket EXCEPT ![i] = 1 + Max({ticket[j] : j \in Proc})]
  /\ ticket' \in [Proc -> Nat]

EnterCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "wait"
  /\ \A j \in Proc: (j # i) => (pc[j] # "cs")
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED ticket

Exit(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED pc

Idle(i) ==
  /\ i \in Proc
  /\ pc[i] = "exit"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ UNCHANGED ticket

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
  \/ \E i \in Proc: Acquire(i)
  \/ \E i \in Proc: EnterCS(i)
  \/ \E i \in Proc: Exit(i)
  \/ \E i \in Proc: Idle(i)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<pc, ticket>>

(*-----------------------------------------------------------------
  Safety invariants (as required)
-----------------------------------------------------------------*)
MutualExclusion ==
  \A i, j \in Proc: (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

TypeOK ==
  /\ pc \in [Proc -> PCSet]
  /\ ticket \in [Proc -> Nat]

Inv == MutualExclusion /\ TypeOK

(*-----------------------------------------------------------------
  State constraint to keep tickets below MaxNat (prune larger values)
-----------------------------------------------------------------*)
StateConstraint == \A i \in Proc: ticket[i] < MaxNat

=============================================================================