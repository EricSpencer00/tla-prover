---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANT N, MaxNat, Nat

\* The set Nat is overridden to be the finite range 0..MaxNat
Nat == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES pc, ticket

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
ProcSet == 1 .. N
NoProc  == 0

\* ----------------------------------------------------------------------
\* Initialization (type-correct arbitrary state)
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [i \in ProcSet |-> "idle"]
  /\ ticket = [i \in ProcSet |-> NoProc]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [ProcSet -> {"idle", "wait", "cs"}]
  /\ ticket \in [ProcSet -> Nat]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Request(i) ==
  /\ pc[i] = "idle"
  /\ pc'    = [pc EXCEPT ![i] = "wait"]
  /\ ticket' = [ticket EXCEPT ![i] = Max(ticket) + 1]

Enter(i) ==
  /\ pc[i] = "wait"
  /\ \A j \in ProcSet :
        (j # i) => (pc[j] # "cs" \/ ticket[i] < ticket[j] \/ (ticket[i] = ticket[j] /\ i < j))
  /\ pc'    = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED ticket

Exit(i) ==
  /\ pc[i] = "cs"
  /\ pc'    = [pc EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = NoProc]

Next ==
  \/ \E i \in ProcSet: Request(i)
  \/ \E i \in ProcSet: Enter(i)
  \/ \E i \in ProcSet: Exit(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
ISpec ==
  Init /\ [][Next]_<<pc, ticket>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
MutualExclusion ==
  \A i, j \in ProcSet :
    (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Inv == MutualExclusion /\ TypeOK

\* ----------------------------------------------------------------------
\* Theorem (optional, for TLC)
\* ----------------------------------------------------------------------
THEOREM SpecImpliesInv == ISpec => []Inv

====