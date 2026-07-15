---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------
  Configuration constants.  The .cfg file will assign concrete values,
  e.g., N = 3, MaxNat = 3, Nat = 0..MaxNat.
-----------------------------------------------------------------*)
CONSTANT N
CONSTANT MaxNat
CONSTANT Nat

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
Proc == 1..N

(*-----------------------------------------------------------------
  State variables (same as in the original Boulanger spec)
-----------------------------------------------------------------*)
VARIABLES flag, next, ticket, pc

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
TicketRange == 0..MaxNat

(*-----------------------------------------------------------------
  Type correctness predicate (used as a state constraint)
-----------------------------------------------------------------*)
TypeOK == 
    /\ flag \in [Proc -> BOOLEAN]
    /\ next \in Nat
    /\ ticket \in [Proc -> TicketRange]
    /\ pc \in [Proc -> {"L", "P", "R"}]

(*-----------------------------------------------------------------
  Initial state (same as Boulanger but with finite Nat)
-----------------------------------------------------------------*)
Init ==
    /\ flag = [i \in Proc |-> FALSE]
    /\ next = 0
    /\ ticket = [i \in Proc |-> 0]
    /\ pc = [i \in Proc |-> "L"]
    /\ TypeOK

(*-----------------------------------------------------------------
  Actions (identical to the original Boulanger algorithm)
-----------------------------------------------------------------*)
L(i) == 
    /\ pc[i] = "L"
    /\ flag' = [flag EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "P"]
    /\ UNCHANGED <<next, ticket>>

P(i) ==
    /\ pc[i] = "P"
    /\ ticket' = [ticket EXCEPT ![i] = next]
    /\ next' = (next + 1) % (MaxNat + 1)
    /\ pc' = [pc EXCEPT ![i] = "R"]
    /\ UNCHANGED flag

R(i) ==
    /\ pc[i] = "R"
    /\ \A j \in Proc :
          (i # j) => 
            ( \/ ~flag[j]
              \/ (ticket[j] > ticket[i]) 
              \/ (ticket[j] = ticket[i] /\ j > i) )
    /\ flag' = [flag EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "L"]
    /\ UNCHANGED <<next, ticket>>

Next ==
    \/ \E i \in Proc : L(i)
    \/ \E i \in Proc : P(i)
    \/ \E i \in Proc : R(i)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<flag, next, ticket, pc>>

(*-----------------------------------------------------------------
  Safety invariants required by the cfg file
-----------------------------------------------------------------*)
MutualExclusion ==
    \A i, j \in Proc :
        (i # j) => ~(pc[i] = "R" /\ pc[j] = "R")

Inv == 
    /\ TypeOK
    /\ MutualExclusion

=============================================================================