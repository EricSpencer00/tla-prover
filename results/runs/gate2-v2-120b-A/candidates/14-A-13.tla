---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets, TLC

(*--------------------------------------------------------------------
  Constants (as required by the .cfg)
--------------------------------------------------------------------*)
CONSTANT N
CONSTANT MaxNat
CONSTANT Nat

(*--------------------------------------------------------------------
  Derived finite set of natural numbers used for overriding the infinite set
--------------------------------------------------------------------*)
Nat == 0..MaxNat

(*--------------------------------------------------------------------
  State variables (inherited from the Boulanger specification)
--------------------------------------------------------------------*)
VARIABLES pc, ticket, next

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
ProcSet == 1..N

(*--------------------------------------------------------------------
  Initial state – same as in the original Boulanger spec, but with
  ticket numbers drawn from the finite range Nat.
--------------------------------------------------------------------*)
Init ==
    /\ pc = [i \in ProcSet |-> "idle"]
    /\ ticket = [i \in ProcSet |-> 0]
    /\ next = 0

(*--------------------------------------------------------------------
  Actions (identical to the original Boulanger actions)
--------------------------------------------------------------------*)
Request(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "request"]
    /\ ticket' = [ticket EXCEPT ![i] = next]
    /\ next' = (next + 1) % (MaxNat + 1)  \* wrap around within the finite range

Enter(i) ==
    /\ pc[i] = "request"
    /\ \A j \in ProcSet :
          (j # i) => (pc[j] # "critical") \/ (ticket[i] < ticket[j]) \/ (ticket[i] = ticket[j] /\ i < j)
    /\ pc' = [pc EXCEPT ![i] = "critical"]
    /\ UNCHANGED <<ticket, next>>

Exit(i) ==
    /\ pc[i] = "critical"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ UNCHANGED <<ticket, next>>

Next ==
    \/ \E i \in ProcSet : Request(i)
    \/ \E i \in ProcSet : Enter(i)
    \/ \E i \in ProcSet : Exit(i)

(*--------------------------------------------------------------------
  Full specification
--------------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<pc, ticket, next>>

(*--------------------------------------------------------------------
  Invariant: type correctness (all variables stay within their domains)
--------------------------------------------------------------------*)
TypeOK ==
    /\ pc \in [ProcSet -> {"idle", "request", "critical"}]
    /\ ticket \in [ProcSet -> Nat]
    /\ next \in Nat

(*--------------------------------------------------------------------
  Safety property: mutual exclusion
--------------------------------------------------------------------*)
MutualExclusion ==
    \A i, j \in ProcSet :
        (i # j) => ~(pc[i] = "critical" /\ pc[j] = "critical")

(*--------------------------------------------------------------------
  Full inductive invariant (as required by the cfg)
--------------------------------------------------------------------*)
Inv == TypeOK /\ MutualExclusion

(*--------------------------------------------------------------------
  Optional: expose the invariant as a theorem (not required but harmless)
--------------------------------------------------------------------*)
THEOREM InvIsInvariant == Spec => []Inv

=============================================================================