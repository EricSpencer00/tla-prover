---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences

CONSTANTS N, MaxNat, Nat

(*--------------------------------------------------------------------
  Finite natural numbers 0..MaxNat (override the infinite Nat set)
--------------------------------------------------------------------*)
Nat == 0 .. MaxNat

VARIABLES pc, ticket, nextTicket

(*--------------------------------------------------------------------
  pc[p]   : program counter of process p
  ticket[p] : ticket number of process p (in Nat)
  nextTicket : the next ticket number to be handed out (in Nat)
--------------------------------------------------------------------*)

ProcSet == 1 .. N
PCVals == {"idle", "request", "wait", "cs", "exit"}

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ pc = [p \in ProcSet |-> "idle"]
    /\ ticket = [p \in ProcSet |-> 0]
    /\ nextTicket = 0
    /\ UNCHANGED << >>

(*--------------------------------------------------------------------
  Actions for a single process p
--------------------------------------------------------------------*)
Request(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "request"]
    /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
    /\ nextTicket' = (nextTicket + 1) % (MaxNat + 1)   \* wrap within Nat
    /\ UNCHANGED << >>

Wait(p) ==
    /\ pc[p] = "request"
    /\ \A q \in ProcSet :
          ( (q # p) => 
              ( (pc[q] # "cs") \/ (ticket[q] > ticket[p]) \/ 
                (ticket[q] = ticket[p] /\ q > p) ) )
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED << ticket, nextTicket >>

Exit(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ ticket' = [ticket EXCEPT ![p] = 0]
    /\ UNCHANGED nextTicket

Other(p) ==
    /\ pc[p] \notin {"idle", "cs"}
    /\ UNCHANGED << pc, ticket, nextTicket >>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ \E p \in ProcSet: Request(p)
    \/ \E p \in ProcSet: Wait(p)
    \/ \E p \in ProcSet: Exit(p)
    \/ \E p \in ProcSet: Other(p)

(*--------------------------------------------------------------------
  Full specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<pc, ticket, nextTicket>>

(*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*)
MutualExclusion ==
    \A p, q \in ProcSet :
        (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

TypeOK ==
    /\ pc \in [ProcSet -> PCVals]
    /\ ticket \in [ProcSet -> Nat]
    /\ nextTicket \in Nat

(* The original Boulanger invariant is named Inv in the cfg *)
Inv ==
    /\ MutualExclusion
    /\ TypeOK

(*--------------------------------------------------------------------
  State constraint: all ticket numbers stay strictly below MaxNat
--------------------------------------------------------------------*)
StateConstraint ==
    \A p \in ProcSet : ticket[p] < MaxNat

(*--------------------------------------------------------------------
  The set of invariants required by the cfg
--------------------------------------------------------------------*)
INVARS == { MutualExclusion, TypeOK, Inv }

(*--------------------------------------------------------------------
  Optional: expose the actions as named operators for readability
--------------------------------------------------------------------*)
RequestAction == Request
WaitAction    == Wait
ExitAction    == Exit

=============================================================================