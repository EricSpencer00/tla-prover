---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANT N, MaxNat

\* ----------------------------------------------------------------------
\* Finite override for the infinite set Nat.  The model checker will use
\* NatOverride wherever Nat would appear in the original Boulanger
\* specification.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* Include the full Boulanger mutual‑exclusion specification.
\* ----------------------------------------------------------------------
INSTANCE Boulanger

\* ----------------------------------------------------------------------
\* Aliases for the components inherited from Boulanger.
\* ----------------------------------------------------------------------
Init == Boulanger!Init
Next == Boulanger!Next
vars == Boulanger!vars

\* ----------------------------------------------------------------------
\* State constraint: ticket numbers must stay strictly below MaxNat.
\* (The variable `ticket` is defined in the Boulanger module as a map
\*  from process identifiers to natural numbers.)
\* ----------------------------------------------------------------------
TicketBound == \A i \in 1..N : ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\* Specification used by the model checker.  It combines the original
\* initialization and step relation with the additional state constraint.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ []TicketBound

\* ----------------------------------------------------------------------
\* Invariants required by the configuration file.
\* ----------------------------------------------------------------------
MutualExclusion == Boulanger!MutualExclusion
TypeOK           == Boulanger!TypeOK
Inv              == Boulanger!Inv

====