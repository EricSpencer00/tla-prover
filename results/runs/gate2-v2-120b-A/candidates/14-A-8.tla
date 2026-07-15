---- MODULE MCBoulanger ----
EXTENDS Naturals, TLC

CONSTANTS N, MaxNat

(* 
  Override the infinite set of natural numbers with a finite range.
  The configuration file will bind Nat to the set 0..MaxNat.
*)
Nat == 0..MaxNat

VARIABLES pc, ticket, nextTicket

(*--------------------------------------------------------------------
  State variables
  pc          : [proc -> {"idle", "request", "wait", "cs", "exit"}]
  ticket      : [proc -> Nat]      (ticket numbers, always < MaxNat)
  nextTicket  : Nat                (next ticket to assign)
--------------------------------------------------------------------*)

(*--------------------------------------------------------------------
  Derived set of processes
--------------------------------------------------------------------*)
Proc == 1..N

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
IsIdle(p) == pc[p] = "idle"
IsRequest(p) == pc[p] = "request"
IsWait(p) == pc[p] = "wait"
IsCS(p) == pc[p] = "cs"
IsExit(p) == pc[p] = "exit"

(*--------------------------------------------------------------------
  Initial predicate
--------------------------------------------------------------------*)
Init ==
  /\ pc = [p \in Proc |-> "idle"]
  /\ ticket = [p \in Proc |-> 0]
  /\ nextTicket = 0

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
Request(p) ==
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "request"]
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = (nextTicket + 1) % MaxNat
  /\ UNCHANGED << >>

Acquire(p) ==
  /\ pc[p] = "request"
  /\ \A q \in Proc: 
        pc[q] # "cs" => 
          ( (ticket[p] # ticket[q]) \/ (ticket[p] # ticket[q] /\ p < q) )
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED << ticket, nextTicket >>

Release(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED << ticket, nextTicket >>

(*--------------------------------------------------------------------
  Next-state relation (stuttering included)
--------------------------------------------------------------------*)
Next ==
  \/ \E p \in Proc: Request(p)
  \/ \E p \in Proc: Acquire(p)
  \/ \E p \in Proc: Release(p)
  \/ UNCHANGED << pc, ticket, nextTicket >>

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<pc, ticket, nextTicket>>

(*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*)
MutualExclusion ==
  \A p, q \in Proc: (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

TypeOK ==
  /\ pc \in [Proc -> {"idle", "request", "wait", "cs", "exit"}]
  /\ ticket \in [Proc -> Nat]
  /\ nextTicket \in Nat

Inv == MutualExclusion /\ TypeOK

(*--------------------------------------------------------------------
  State constraint limiting ticket numbers strictly below MaxNat
--------------------------------------------------------------------*)
StateConstraint ==
  /\ \A p \in Proc: ticket[p] < MaxNat

====