---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N, MaxNat, Nat

\*--------------------------------------------------------------------
\*  Type Declarations
\*--------------------------------------------------------------------
TypeOK == 
    /\ N \in Nat
    /\ MaxNat \in Nat
    /\ Nat = 0..MaxNat
    /\ N >= 1
    /\ MaxNat >= 0

\*--------------------------------------------------------------------
\*  State Variables inherited from Bakery (simplified for this module)
\*--------------------------------------------------------------------
VARIABLES ticket, pos, cs

\*--------------------------------------------------------------------
\*  Convenience definitions
\*--------------------------------------------------------------------
Undefined == "\u221e" \* Representation of a unique undefined value

\*--------------------------------------------------------------------
\*  Initialization (same as Bakery but with finite Nat)
\*--------------------------------------------------------------------
Init ==
    /\ ticket = [i \in 1..N |-> 0]
    /\ pos    = [i \in 1..N |-> 0]
    /\ cs     = [i \in 1..N |-> FALSE]

\*--------------------------------------------------------------------
\*  Actions
\*--------------------------------------------------------------------
Request(i) ==
    /\ i \in 1..N
    /\ ticket' = [ticket EXCEPT ![i] = max(Nat) + 1]
    /\ UNCHANGED <<pos, cs>>

Pick(i) ==
    /\ i \in 1..N
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED <<pos, cs>>

Enter(i) ==
    /\ i \in 1..N
    /\ pos' = [pos EXCEPT ![i] = ticket[i]]
    /\ UNCHANGED <<ticket, cs>>

Exit(i) ==
    /\ i \in 1..N
    /\ pos' = [pos EXCEPT ![i] = 0]
    /\ cs' = [cs EXCEPT ![i] = FALSE]
    /\ UNCHANGED ticket

\*--------------------------------------------------------------------
\*  Next state relation (exactly as Bakery)
\*--------------------------------------------------------------------
Next ==
    \/ \E i \in 1..N: Request(i)
    \/ \E i \in 1..N: Pick(i)
    \/ \E i \in 1..N: Enter(i)
    \/ \E i \in 1..N: Exit(i)

\*--------------------------------------------------------------------
\*  Inductive specification (starting from any type-correct state)
\*--------------------------------------------------------------------
ISpec == [] [Init] /\ [][Next]_<<ticket, pos, cs>>

\*--------------------------------------------------------------------
\*  Safety invariants
\*--------------------------------------------------------------------
MutualExclusion ==
    \A i, j \in 1..N : i # j => ~(cs[i] /\ cs[j])

TypeInvariant ==
    /\ ticket \in [1..N -> Nat]
    /\ pos    \in [1..N -> Nat]
    /\ cs     \in [1..N -> BOOLEAN]

Inv ==
    /\ ticket \in [1..N -> Nat]
    /\ pos    \in [1..N -> Nat]
    /\ cs     \in [1..N -> BOOLEAN]
    /\ \A i, j \in 1..N : i # j => 
          \E k \in 1..N : 
              (pos[i] = k /\ pos[j] > k) \/ (pos[i] > pos[j])

\*--------------------------------------------------------------------
\*  Specification to be used by TLC
\*--------------------------------------------------------------------
Spec == ISpec

====