---- MODULE MCBakery ----
EXTENDS Naturals, TLC

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANT N        \* Number of processes (set to 2 in the .cfg)
CONSTANT MaxNat   \* Upper bound for the finite natural numbers (set to 2)
CONSTANT Nat      \* Finite set representing the overridden natural numbers

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
Proc == 1 .. N   \* Set of process identifiers

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES pc, ticket, choosing

(*-----------------------------------------------------------------
  Type definitions (for readability)
-----------------------------------------------------------------*)
PCValues == {"idle", "request", "cs", "exit"}

(*-----------------------------------------------------------------
  TypeOK: type correctness invariant
-----------------------------------------------------------------*)
TypeOK ==
    /\ pc \in [Proc -> PCValues]
    /\ ticket \in [Proc -> Nat]
    /\ choosing \in [Proc -> BOOLEAN]

(*-----------------------------------------------------------------
  Initial state (consistent with the original Bakery spec)
-----------------------------------------------------------------*)
Init ==
    /\ pc = [i \in Proc |-> "idle"]
    /\ ticket = [i \in Proc |-> 0]
    /\ choosing = [i \in Proc |-> FALSE]

(*-----------------------------------------------------------------
  Actions of the Bakery algorithm (standard formulation)
-----------------------------------------------------------------*)
Request(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "request"]
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED ticket

SetTicket(i) ==
    /\ pc[i] = "request"
    /\ choosing[i] = TRUE
    /\ ticket' = [ticket EXCEPT ![i] = Max(ticket) + 1]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ UNCHANGED pc
    /\ UNCHANGED << >>  \* No other variables change

EnterCS(i) ==
    /\ pc[i] = "request"
    /\ choosing[i] = FALSE
    /\ \A j \in Proc :
          (j # i) => 
            /\ ~choosing[j]
            /\ (ticket[i] < ticket[j] \/ (ticket[i] = ticket[j] /\ i < j))
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED << ticket, choosing >>

Exit(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED << ticket, choosing >>

Next ==
    \/ \E i \in Proc: Request(i)
    \/ \E i \in Proc: SetTicket(i)
    \/ \E i \in Proc: EnterCS(i)
    \/ \E i \in Proc: Exit(i)

(*-----------------------------------------------------------------
  Safety invariant: Mutual exclusion
-----------------------------------------------------------------*)
MutualExclusion ==
    \A i, j \in Proc :
        (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(*-----------------------------------------------------------------
  Full inductive invariant (as given by the original spec)
-----------------------------------------------------------------*)
Inv == MutualExclusion /\ TypeOK

(*-----------------------------------------------------------------
  Specification (inductive specification)
-----------------------------------------------------------------*)
ISpec == Init /\ [][Next]_<<pc, ticket, choosing>>

(*-----------------------------------------------------------------
  THEOREM: The specification implies the invariant (optional, for TLC)
-----------------------------------------------------------------*)
THEOREM SpecImpliesInv == ISpec => []Inv

====