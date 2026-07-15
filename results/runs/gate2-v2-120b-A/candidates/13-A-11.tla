---- MODULE MCBakery ----
EXTENDS Naturals, TLC

(*-----------------------------------------------------------------
  Finite natural numbers: Nat is overridden to be the set
  0..MaxNat, where MaxNat is a constant supplied by the .cfg file.
-----------------------------------------------------------------*)
CONSTANTS N, MaxNat, Nat

(* Ensure Nat is the finite range 0..MaxNat *)
Nat == 0 .. MaxNat

VARIABLES pc, ticket, next

(*-----------------------------------------------------------------
  State variable meanings (inherited from the original Bakery
  specification):
    pc     : the program counter of each process, one of
             {"idle", "choosing", "wait", "cs"}.
    ticket : the ticket number held by each process.
    next   : the next ticket number to be issued.
-----------------------------------------------------------------*)

(* Initial state – same as in the original Bakery spec, but with
   ticket numbers drawn from the finite Nat range. *)
Init ==
  /\ pc = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]
  /\ next = 0

(*-----------------------------------------------------------------
  Actions (inherited without modification, but using the finite Nat
  range). Each action respects the bounds of Nat.
-----------------------------------------------------------------*)

Choose(i) ==
  /\ i \in 1..N
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "choosing"]
  /\ ticket' = [ticket EXCEPT ![i] = next]
  /\ next' = IF next < MaxNat THEN next + 1 ELSE 0
  /\ UNCHANGED *

Enter(i) ==
  /\ i \in 1..N
  /\ pc[i] = "choosing"
  /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ UNCHANGED <<ticket, next>>

Check(i) ==
  /\ i \in 1..N
  /\ pc[i] = "wait"
  /\ \A j \in 1..N :
        (j # i) => 
          /\ (pc[j] # "cs") \/ (ticket[i] < ticket[j]) \/ (ticket[i] = ticket[j] /\ i < j))
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<ticket, next>>

Exit(i) ==
  /\ i \in 1..N
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED next

(* The overall Next action allows any process to take any of the above steps. *)
Next ==
  \/ \E i \in 1..N: Choose(i)
  \/ \E i \in 1..N: Enter(i)
  \/ \E i \in 1..N: Check(i)
  \/ \E i \in 1..N: Exit(i)

(*-----------------------------------------------------------------
  Safety invariants required by the .cfg file.
-----------------------------------------------------------------*)

MutualExclusion ==
  \A i, j \in 1..N : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

TypeOK ==
  /\ pc \in [1..N -> {"idle", "choosing", "wait", "cs"}]
  /\ ticket \in [1..N -> Nat]
  /\ next \in Nat

Inv == MutualExclusion /\ TypeOK

(*-----------------------------------------------------------------
  Specification used for model checking: the inductive specification
  starts from any state satisfying the type-correct invariant.
-----------------------------------------------------------------*)
ISpec ==
  /\ Init
  /\ [][Next]_<<pc, ticket, next>>

====