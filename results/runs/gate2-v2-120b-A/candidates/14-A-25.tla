---- MODULE MCBoulanger ----
EXTENDS Naturals, TLC

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANT N
CONSTANT MaxNat
CONSTANT Nat

(*--------------------------------------------------------------------
  State variables (inherited from Boulanger)
--------------------------------------------------------------------*)
VARIABLES pc, token, ticket, choosing, next, last

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
ProcSet == 1..N

(*--------------------------------------------------------------------
  Initial state (same as Boulanger, but with Nat constrained)
--------------------------------------------------------------------*)
Init ==
    /\ pc = [i \in ProcSet |-> "idle"]
    /\ token = [i \in ProcSet |-> 0]
    /\ ticket = [i \in ProcSet |-> 0]
    /\ choosing = [i \in ProcSet |-> FALSE]
    /\ next = 0
    /\ last = [i \in ProcSet |-> 0]

(*--------------------------------------------------------------------
  Actions (inherited from Boulanger, no modification)
--------------------------------------------------------------------*)
Idle(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "request"]
    /\ UNCHANGED << token, ticket, choosing, next, last >>

Request(i) ==
    /\ pc[i] = "request"
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED << pc, token, ticket, next, last >>
    /\ pc' = [pc EXCEPT ![i] = "choose"]
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]

Choose(i) ==
    /\ pc[i] = "choose"
    /\ ticket' = [ticket EXCEPT ![i] = next]
    /\ next' = (next + 1) % (MaxNat + 1)
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "wait"]
    /\ UNCHANGED << token, last >>

Wait(i) ==
    LET
        lower == \A j \in ProcSet :
                    /\ j # i => 
                       ( /\ ~choosing[j]
                         /\ (ticket[j] = 0 \/ ticket[i] = 0 \/ 
                             ticket[i] < ticket[j] \/ 
                             (ticket[i] = ticket[j] /\ i < j) ) )
    IN
    /\ pc[i] = "wait"
    /\ lower
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED << token, ticket, choosing, next, last >>

LeaveCS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED << token, ticket, choosing, next, last >>

Next ==
    \E i \in ProcSet :
        \/ Idle(i)
        \/ Request(i)
        \/ Choose(i)
        \/ Wait(i)
        \/ LeaveCS(i)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<pc, token, ticket, choosing, next, last>>

(*--------------------------------------------------------------------
  Safety invariants (from Boulanger)
--------------------------------------------------------------------*)
MutualExclusion ==
    \A i, j \in ProcSet :
        (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

TypeOK ==
    /\ pc \in [ProcSet -> {"idle", "request", "choose", "wait", "cs"}]
    /\ token \in [ProcSet -> Nat]
    /\ ticket \in [ProcSet -> Nat]
    /\ choosing \in [ProcSet -> BOOLEAN]
    /\ next \in Nat
    /\ last \in [ProcSet -> Nat]

Inv ==
    /\ MutuaLExclusion
    /\ TypeOK
    /\ /\ \A i \in ProcSet : ticket[i] < MaxNat

(*--------------------------------------------------------------------
  State constraint to keep ticket numbers below MaxNat
--------------------------------------------------------------------*)
StateConstraint == \A i \in ProcSet : ticket[i] < MaxNat

(*--------------------------------------------------------------------
  Theorem (optional, to silence dead code warnings)
--------------------------------------------------------------------*)
THEOREM Spec => []Inv

====