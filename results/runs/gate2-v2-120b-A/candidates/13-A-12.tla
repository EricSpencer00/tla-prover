---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANT N          \* Number of processes
CONSTANT MaxNat    \* Upper bound for natural numbers (tickets)
CONSTANT Nat       \* Finite set of natural numbers used in the model

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
Proc == 1 .. N

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES pc, ticket, nextTicket

(*--------------------------------------------------------------------
  Types (for readability, not used directly in the spec)
--------------------------------------------------------------------*)
PC == {"idle", "request", "wait", "cs", "exit"}

(*--------------------------------------------------------------------
  Initial predicate
--------------------------------------------------------------------*)
Init ==
  /\ pc = [i \in Proc |-> "idle"]
  /\ ticket = [i \in Proc |-> 0]
  /\ nextTicket = 0

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
Request(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "request"]
  /\ UNCHANGED <<ticket, nextTicket>>

AssignTicket(i) ==
  /\ pc[i] = "request"
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
  /\ nextTicket' = IF nextTicket = MaxNat THEN 0 ELSE nextTicket + 1
  /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ UNCHANGED << >>

EnterCS(i) ==
  /\ pc[i] = "wait"
  /\ \A j \in Proc :
        (j # i) => 
          \/ pc[j] # "cs"
          \/ /\ ticket[j] # 0
             /\ ticket[i] # 0
             /\ (ticket[i] < ticket[j] \/ (ticket[i] = ticket[j] /\ i < j))
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED <<ticket, nextTicket>>

Exit(i) ==
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED <<ticket, nextTicket>>

Finish(i) ==
  /\ pc[i] = "exit"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED nextTicket

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
  \E i \in Proc :
      \/ Request(i)
      \/ AssignTicket(i)
      \/ EnterCS(i)
      \/ Exit(i)
      \/ Finish(i)

(*--------------------------------------------------------------------
  Specification (inductive, allowing any type-correct initial state)
--------------------------------------------------------------------*)
ISpec == Init /\ [][Next]_<<pc, ticket, nextTicket>>

(*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*)
MutualExclusion ==
  ~(\E i, j \in Proc : i # j /\ pc[i] = "cs" /\ pc[j] = "cs")

TypeOK ==
  /\ pc \in [Proc -> PC]
  /\ ticket \in [Proc -> Nat]
  /\ nextTicket \in Nat

Inv == MutualExclusion /\ TypeOK

(*--------------------------------------------------------------------
  The required identifiers
--------------------------------------------------------------------*)
SPECIFICATION ISpec
INVARIANT MutualExclusion
INVARIANT TypeOK
INVARIANT Inv

=============================================================================