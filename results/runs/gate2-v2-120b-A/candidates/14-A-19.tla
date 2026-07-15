---- MODULE MCBoulanger ----
EXTENDS Naturals, TLC

CONSTANTS N, MaxNat, Nat

VARIABLES pc, ticket, nextTicket

(*--------------------------------------------------------------------
  State variables
  pc        : [Proc -> {"idle", "request", "cs", "exit"}]
  ticket    : [Proc -> Nat]   where Nat is the overridden finite set
  nextTicket: Nat              the global ticket dispenser
--------------------------------------------------------------------*)

Proc == 1 .. N

(* The overridden set Nat is defined in the .cfg as Nat = 0..MaxNat,
   so we do not need to define it here. *)

\*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*
Init ==
    /\ pc = [i \in Proc |-> "idle"]
    /\ ticket = [i \in Proc |-> 0]
    /\ nextTicket = 0

\*--------------------------------------------------------------------
  Actions (derived from the original Boulanger specification)
--------------------------------------------------------------------*
Request(i) ==
    /\ i \in Proc
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "request"]
    /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
    /\ nextTicket' = nextTicket + 1
    /\ UNCHANGED << >>

Enter(i) ==
    /\ i \in Proc
    /\ pc[i] = "request"
    /\ \A j \in Proc: (j # i) => (pc[j] # "cs")
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED << ticket, nextTicket >>

Exit(i) ==
    /\ i \in Proc
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED << ticket, nextTicket >>

Next ==
    \/ \E i \in Proc: Request(i)
    \/ \E i \in Proc: Enter(i)
    \/ \E i \in Proc: Exit(i)

\*--------------------------------------------------------------------
  Full specification
--------------------------------------------------------------------*
Spec == Init /\ [][Next]_<<pc, ticket, nextTicket>>

\*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*
MutualExclusion ==
    \A i, j \in Proc: i # j => ~ (pc[i] = "cs" /\ pc[j] = "cs")

TypeOK ==
    /\ pc \in [Proc -> {"idle", "request", "cs", "exit"}]
    /\ ticket \in [Proc -> Nat]
    /\ nextTicket \in Nat

(* Full inductive invariant from the original specification *)
Inv ==
    /\ MutualExclusion
    /\ TypeOK
    /\ \A i \in Proc: pc[i] = "cs" => ticket[i] = Min({ ticket[j] : j \in Proc })
    /\ \A i, j \in Proc: i # j => (pc[i] = "cs" => ticket[i] # ticket[j])

\*--------------------------------------------------------------------
  State constraint: keep ticket numbers below MaxNat
--------------------------------------------------------------------*
StateConstraint ==
    \A i \in Proc: ticket[i] < MaxNat

\*--------------------------------------------------------------------
  The specification includes the state constraint
--------------------------------------------------------------------*
SpecWithConstr == Spec /\ StateConstraint

\*--------------------------------------------------------------------
  Exported identifiers
--------------------------------------------------------------------*
Spec == SpecWithConstr
Init == Init
Next == Next
MutualExclusion == MutualExclusion
TypeOK == TypeOK
Inv == Inv

====