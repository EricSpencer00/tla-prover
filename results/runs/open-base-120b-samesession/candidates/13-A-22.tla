---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N, MaxNat

\* ----------------------------------------------------------------------
\* Finite version of the natural numbers used for model checking
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES pc, choosing, number

vars == << pc, choosing, number >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
MaxNumber(num) ==
  IF ∃ j \in 1..N : num[j] # 0
    THEN Max({ num[j] : j \in 1..N })
    ELSE 0

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [i \in 1..N |-> "idle"]
  /\ choosing = [i \in 1..N |-> FALSE]
  /\ number = [i \in 1..N |-> 0]

\* ----------------------------------------------------------------------
\* Actions of each process i
\* ----------------------------------------------------------------------
Request(i) ==
  /\ pc[i] = "idle"
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ number'   = [number EXCEPT ![i] = (MaxNumber(number) + 1) % (MaxNat + 1)]
  /\ UNCHANGED pc

Enter(i) ==
  /\ pc[i] = "waiting"
  /\ choosing[i] = FALSE
  /\ \A j \in 1..N :
        ( number[j] = 0
          \/ ( number[i] < number[j] )
          \/ ( number[i] = number[j] /\ i < j ) )
  /\ pc' = [pc EXCEPT ![i] = "critical"]
  /\ UNCHANGED << choosing, number >>

Release(i) ==
  /\ pc[i] = "critical"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ number' = [number EXCEPT ![i] = 0]
  /\ UNCHANGED choosing

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : Release(i)

\* ----------------------------------------------------------------------
\* Specification (inductive)
\* ----------------------------------------------------------------------
ISpec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [1..N -> {"idle", "waiting", "critical"}]
  /\ choosing \in [1..N -> BOOLEAN]
  /\ number \in [1..N -> NatOverride]

MutualExclusion ==
  \A i, j \in 1..N :
    ( i # j ) => ~( pc[i] = "critical" /\ pc[j] = "critical" )

Inv == TypeOK /\ MutualExclusion

\* ----------------------------------------------------------------------
\* Exported identifiers (required by the .cfg file)
\* ----------------------------------------------------------------------
\* CONSTANTS: N, MaxNat
\* SPECIFICATION formula: ISpec
\* INVARIANTS: MutualExclusion, TypeOK, Inv
\* NatOverride replaces Nat from Naturals (Nat itself is not re‑declared)

====