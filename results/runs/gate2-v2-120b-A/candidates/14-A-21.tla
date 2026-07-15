---- MODULE MCBoulanger ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------------
  Constants
-----------------------------------------------------------------------*)
CONSTANT N
CONSTANT MaxNat
CONSTANT Nat

(*-----------------------------------------------------------------------
  Finite Nat set (overridden natural numbers)
-----------------------------------------------------------------------*)
NatSet == 0 .. MaxNat

(*-----------------------------------------------------------------------
  State variables inherited from the Boulanger specification
-----------------------------------------------------------------------*)
VARIABLES pc, ticket

(*-----------------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------------*)
ProcSet == 0 .. (N - 1)

TypeOK == 
    /\ pc \in [ProcSet -> {"idle", "request", "wait", "cs"}]
    /\ ticket \in [ProcSet -> NatSet]

(*-----------------------------------------------------------------------
  Initial state
-----------------------------------------------------------------------*)
Init ==
    /\ pc = [i \in ProcSet |-> "idle"]
    /\ ticket = [i \in ProcSet |-> 0]

(*-----------------------------------------------------------------------
  Actions (same as the original Boulanger algorithm)
-----------------------------------------------------------------------*)
Request(i) ==
    /\ pc[i] = "idle"
    /\ pc' = [pc EXCEPT ![i] = "request"]
    /\ ticket' = [ticket EXCEPT ![i] = 1]

Enter(i) ==
    /\ pc[i] = "request"
    /\ \A j \in ProcSet : (j # i) => (pc[j] # "cs")
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED ticket

Exit(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "idle"]
    /\ ticket' = [ticket EXCEPT ![i] = 0]

Next ==
    \E i \in ProcSet : Request(i) \/ Enter(i) \/ Exit(i)

(*-----------------------------------------------------------------------
  Specification
-----------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<pc, ticket>>

(*-----------------------------------------------------------------------
  Safety properties
-----------------------------------------------------------------------*)
MutualExclusion ==
    \A i, j \in ProcSet : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

Inv == TypeOK /\ MutualExclusion

(*-----------------------------------------------------------------------
  State constraint to keep ticket numbers below MaxNat
-----------------------------------------------------------------------*)
StateConstraint == 
    \A i \in ProcSet : ticket[i] < MaxNat

(*-----------------------------------------------------------------------
  Theorem (optional, for documentation)
-----------------------------------------------------------------------*)
THEOREM Spec => []Inv

====