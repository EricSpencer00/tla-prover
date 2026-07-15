---- MODULE MCBoulanger ----
EXTENDS Naturals, TLC

(*--------------------------------------------------------------------
  Constants
 --------------------------------------------------------------------*)
CONSTANT N          \* number of processes (set in the .cfg)
CONSTANT MaxNat     \* maximal value for the overridden natural numbers
CONSTANT Nat        \* finite set of natural numbers used for ticket values

(*--------------------------------------------------------------------
  Derived sets
 --------------------------------------------------------------------*)
Proc == 1 .. N

(*--------------------------------------------------------------------
  State variables (inherited from Boulanger)
 --------------------------------------------------------------------*)
VARIABLES pc, ticket, choosing

(*--------------------------------------------------------------------
  Type correctness (for readability)
 --------------------------------------------------------------------*)
TypeOK ==
  /\ pc \in [Proc -> {"idle", "enter", "cs", "exit"}]
  /\ ticket \in [Proc -> Nat]
  /\ choosing \in [Proc -> BOOLEAN]

(*--------------------------------------------------------------------
  Initial state (inherits Boulanger's INIT, with Nat bounded)
 --------------------------------------------------------------------*)
BInit ==
  /\ pc = [i \in Proc |-> "idle"]
  /\ ticket = [i \in Proc |-> 0]
  /\ choosing = [i \in Proc |-> FALSE]

Init == BInit

(*--------------------------------------------------------------------
  Actions (inherit Boulanger's actions, unchanged)
 --------------------------------------------------------------------*)

Idle(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "enter"]
  /\ UNCHANGED << ticket, choosing >>

RequestCS(i) ==
  /\ pc[i] = "enter"
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ UNCHANGED << pc, ticket >>

TakeTicket(i) ==
  /\ pc[i] = "enter"
  /\ choosing[i] = TRUE
  /\ ticket' = [ticket EXCEPT ![i] = 1 + Max({ ticket[j] : j \in Proc })]
  /\ UNCHANGED << pc, choosing >>

FinishTicket(i) ==
  /\ pc[i] = "enter"
  /\ choosing[i] = TRUE
  /\ ticket' = [ticket EXCEPT ![i] = ticket[i]]
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ UNCHANGED pc

Wait(i) ==
  /\ pc[i] = "enter"
  /\ choosing[i] = FALSE
  /\ \A j \in Proc :
        (j # i) =>
          /\ (choosing[j] = FALSE)
          /\ (ticket[j] = 0 \/ ticket[i] < ticket[j] \/ (ticket[i] = ticket[j] /\ i < j))
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << ticket, choosing >>

ExitCS(i) ==
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED << ticket, choosing >>

Reset(i) ==
  /\ pc[i] = "exit"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED choosing

(*--------------------------------------------------------------------
  Next-state relation
 --------------------------------------------------------------------*)
BNext ==
  \E i \in Proc :
    \/ Idle(i)
    \/ RequestCS(i)
    \/ TakeTicket(i)
    \/ FinishTicket(i)
    \/ Wait(i)
    \/ ExitCS(i)
    \/ Reset(i)

Next == BNext

(*--------------------------------------------------------------------
  Specification
 --------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<pc, ticket, choosing>>

(*--------------------------------------------------------------------
  Safety invariants (inherited from Boulanger)
 --------------------------------------------------------------------*)

MutualExclusion ==
  \A i, j \in Proc :
    (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

(* Full inductive invariant, same as Boulanger's Inv *)
Inv ==
  /\ TypeOK
  /\ MutualExclusion

=============================================================================