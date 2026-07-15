---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, MaxNat, Nat

\* ----------------------------------------------------------------------
\* Variables (same as in the original Bakery specification)
\* ----------------------------------------------------------------------
VARIABLES pc,         \* program counter per process
          ticket,     \* ticket numbers per process
          chooser,    \* the last ticket number chosen
          turn        \* the current turn

\* ----------------------------------------------------------------------
\* Finite natural numbers (overridden Nat)
\* ----------------------------------------------------------------------
NatRange == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
ProcSet == 1 .. N
ValueSet == NatRange

\* ----------------------------------------------------------------------
\* Initial state (type‑correct and within the finite range)
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [i \in ProcSet |-> "idle"]
  /\ ticket = [i \in ProcSet |-> 0]
  /\ chooser = 0
  /\ turn = 1

\* ----------------------------------------------------------------------
\* Actions (identical to the original Bakery algorithm)
\* ----------------------------------------------------------------------
Enter(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![i] = chooser + 1]
  /\ chooser' = chooser + 1
  /\ UNCHANGED <<turn>>

Waiting(i) ==
  /\ pc[i] = "waiting"
  /\ \A j \in ProcSet :
        (j # i) =>
          (pc[j] # "crit" =>
            (ticket[j] = 0) \/ (ticket[i] < ticket[j]) \/ (ticket[i] = ticket[j] /\ i < j))
  /\ pc' = [pc EXCEPT ![i] = "crit"]
  /\ UNCHANGED <<ticket, chooser, turn>>

Exit(i) ==
  /\ pc[i] = "crit"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED <<chooser, turn>>

Next ==
  \E i \in ProcSet :
    \/ Enter(i)
    \/ Waiting(i)
    \/ Exit(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
ISpec == Init /\ [][Next]_<<pc, ticket, chooser, turn>>

\* ----------------------------------------------------------------------
\* Safety properties (invariants)
\* ----------------------------------------------------------------------
MutualExclusion ==
  \A i, j \in ProcSet :
    (i # j) => ~(pc[i] = "crit" /\ pc[j] = "crit")

TypeOK ==
  /\ pc \in [ProcSet -> {"idle", "waiting", "crit"}]
  /\ ticket \in [ProcSet -> ValueSet]
  /\ chooser \in NatRange
  /\ turn \in ProcSet

Inv == MutualExclusion /\ TypeOK

=============================================================================