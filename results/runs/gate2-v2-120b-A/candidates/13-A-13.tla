---- MODULE MCBakery ----
EXTENDS Naturals, TLC

(*-----------------------------------------------------------------
  Constants (to be set in the .cfg file)
-----------------------------------------------------------------*)
CONSTANT N          \* number of processes
CONSTANT MaxNat    \* maximal natural number used for tickets
CONSTANT Nat       \* finite set of natural numbers (0..MaxNat)

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
Proc == 1..N
Ticket == Nat

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES pc, ticket, choosing

vars == <<pc, ticket, choosing>>

(*-----------------------------------------------------------------
  Initial predicate
-----------------------------------------------------------------*)
Init ==
  /\ pc = [i \in Proc |-> "idle"]
  /\ ticket = [i \in Proc |-> 0]
  /\ choosing = [i \in Proc |-> FALSE]

(*-----------------------------------------------------------------
  Actions (same as in the original Bakery algorithm)
-----------------------------------------------------------------*)
Enter(i) ==
  /\ i \in Proc
  /\ pc[i] = "idle"
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<pc, ticket>>
  /\ pc' = pc
  /\ ticket' = ticket

AssignTicket(i) ==
  /\ i \in Proc
  /\ choosing[i] = TRUE
  /\ ticket' = [ticket EXCEPT ![i] = 1 + Max({ ticket[j] : j \in Proc })]
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ UNCHANGED pc

Wait(i) ==
  /\ i \in Proc
  /\ pc[i] = "idle"
  /\ choosing[i] = FALSE
  /\ \A j \in Proc :
        /\ j = i \/ 
           /\ pc[j] = "idle"
           \/ /\ ~choosing[j]
              /\ (ticket[i] < ticket[j] \/
                  /\ ticket[i] = ticket[j] /\ i < j)
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<ticket, choosing>>

Leave(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED choosing

(*-----------------------------------------------------------------
  Next-state relation (any one action of any process)
-----------------------------------------------------------------*)
Next ==
  \E i \in Proc :
    \/ Enter(i)
    \/ AssignTicket(i)
    \/ Wait(i)
    \/ Leave(i)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
ISpec == Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Invariant definitions
-----------------------------------------------------------------*)
MutualExclusion ==
  \A i, j \in Proc :
    (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

TypeOK ==
  /\ pc \in [Proc -> {"idle", "cs"}]
  /\ ticket \in [Proc -> Ticket]
  /\ choosing \in [Proc -> BOOLEAN]

Inv == MutualExclusion /\ TypeOK

=============================================================================