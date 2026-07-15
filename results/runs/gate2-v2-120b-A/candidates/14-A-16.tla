---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  Constants (as required by the .cfg)
--------------------------------------------------------------------*)
CONSTANT N
CONSTANT MaxNat
CONSTANT Nat

(*--------------------------------------------------------------------
  Derived constant: the set of process identifiers
--------------------------------------------------------------------*)
ProcSet == 1 .. N

(*--------------------------------------------------------------------
  Type definitions (used for readability)
--------------------------------------------------------------------*)
StateVar == {"pc", "req", "ticket"}

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES pc, req, ticket

(*--------------------------------------------------------------------
  TypeOK: state constraint that ensures variables stay within expected ranges.
  This also serves as the state constraint required by the description.
--------------------------------------------------------------------*)
TypeOK ==
  /\ pc \in [ProcSet -> {"idle", "request", "wait", "cs"}]
  /\ req \in [ProcSet -> BOOLEAN]
  /\ ticket \in [ProcSet -> Nat]

(*--------------------------------------------------------------------
  Initial state (same as Boulanger, but with Nat limited to 0..MaxNat)
--------------------------------------------------------------------*)
Init ==
  /\ pc = [i \in ProcSet |-> "idle"]
  /\ req = [i \in ProcSet |-> FALSE]
  /\ ticket = [i \in ProcSet |-> 0]

(*--------------------------------------------------------------------
  Actions (identical to Boulanger)
--------------------------------------------------------------------*)
Request(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "idle"
  /\ req' = [req EXCEPT ![i] = TRUE]
  /\ ticket' = [ticket EXCEPT ![i] = Max(ticket) + 1]
  /\ pc' = [pc EXCEPT ![i] = "request"]
  /\ UNCHANGED << >>

Enter(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "request"
  /\ \A j \in ProcSet :
        (j # i) => ( ~req[j] \/ ticket[i] < ticket[j] )
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << req, ticket >>

Exit(i) ==
  /\ i \in ProcSet
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ req' = [req EXCEPT ![i] = FALSE]
  /\ UNCHANGED ticket

Next ==
  \/ \E i \in ProcSet: Request(i)
  \/ \E i \in ProcSet: Enter(i)
  \/ \E i \in ProcSet: Exit(i)

(*--------------------------------------------------------------------
  Full specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<pc, req, ticket>>

(*--------------------------------------------------------------------
  Safety invariants (as required by the .cfg)
--------------------------------------------------------------------*)
MutualExclusion ==
  \A i, j \in ProcSet :
    (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

Inv == TypeOK

=============================================================================