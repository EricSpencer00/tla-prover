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
\* Concrete definitions for the parameters required by the Boulanger
\* specification.  They are expressed in terms of the constants N and
\* MaxNat that are supplied by the configuration file.
\* ----------------------------------------------------------------------
INSTANCE Boulanger WITH
    num       <- N,
    max       <- MaxNat,
    previous  <- [i \in 1..N |-> 0],
    nxt       <- [i \in 1..N |-> 0],
    unchecked <- {},
    pc        <- [i \in 1..N |-> "idle"],
    flag      <- [i \in 1..N |-> FALSE]

\* ----------------------------------------------------------------------
\* State constraint: ticket numbers must stay strictly below MaxNat.
\* (The variable `ticket` is defined in the Boulanger module as a map
\*  from process identifiers to natural numbers.)
\* ----------------------------------------------------------------------
TicketBound == \A i \in 1..N : Boulanger!ticket[i] < MaxNat

\* ----------------------------------------------------------------------
\* Specification used by the model checker.  It combines the original
\* initialization and step relation with the additional state
\* constraint.
\* ----------------------------------------------------------------------
Spec == Boulanger!Init /\ [][Boulanger!Next]_(Boulanger!vars) /\ []TicketBound

\* ----------------------------------------------------------------------
\* Invariants required by the configuration file.
\* ----------------------------------------------------------------------
MutualExclusion == Boulanger!MutualExclusion
TypeOK           == Boulanger!TypeOK
Inv              == Boulanger!Inv
====