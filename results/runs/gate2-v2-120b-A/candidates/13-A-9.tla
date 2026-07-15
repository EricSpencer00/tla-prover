---- MODULE MCBakery ----
EXTENDS Naturals, TLC

(*--------------------------------------------------------------------
  Constants
  --------------------------------------------------------------------*)
CONSTANT N, MaxNat

(* Override the natural numbers with a finite range *)
Nat == 0 .. MaxNat

(*--------------------------------------------------------------------
  Derived sets
  --------------------------------------------------------------------*)
Proc == 0 .. N-1

(*--------------------------------------------------------------------
  State variables
  --------------------------------------------------------------------*)
VARIABLES pc, ticket

(*--------------------------------------------------------------------
  Types
  --------------------------------------------------------------------*)
PcType == {"idle", "wait", "critical", "exit"}
TicketType == Nat

(*--------------------------------------------------------------------
  Initial predicate (type-correct state)
  --------------------------------------------------------------------*)
Init ==
  /\ pc = [i \in Proc |-> "idle"]
  /\ ticket = [i \in Proc |-> 0]

(*--------------------------------------------------------------------
  Actions (same as classic Bakery algorithm)
  --------------------------------------------------------------------*)
Enter(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "wait"]
  /\ ticket' = ticket

Acquire(i) ==
  /\ pc[i] = "wait"
  /\ LET new == Max(ticket) + 1 IN
        /\ new \in Nat
        /\ ticket' = [ticket EXCEPT ![i] = new]
  /\ pc' = [pc EXCEPT ![i] = "critical"]
  /\ UNCHANGED pc
  /\ UNCHANGED ticket

Exit(i) ==
  /\ pc[i] = "critical"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED ticket

Done(i) ==
  /\ pc[i] = "exit"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = 0]

Next ==
  \E i \in Proc :
      Enter(i) \/ Acquire(i) \/ Exit(i) \/ Done(i)

(*--------------------------------------------------------------------
  Specification
  --------------------------------------------------------------------*)
ISpec == Init /\ [][Next]_<<pc, ticket>>

(*--------------------------------------------------------------------
  Invariant: mutual exclusion
  --------------------------------------------------------------------*)
MutualExclusion ==
  Cardinality({i \in Proc : pc[i] = "critical"}) <= 1

(*--------------------------------------------------------------------
  Type correctness invariant
  --------------------------------------------------------------------*)
TypeOK ==
  /\ pc \in [Proc -> PcType]
  /\ ticket \in [Proc -> TicketType]

(*--------------------------------------------------------------------
  Full inductive invariant (conjunction of safety properties)
  --------------------------------------------------------------------*)
Inv == MutualExclusion /\ TypeOK

=============================================================================