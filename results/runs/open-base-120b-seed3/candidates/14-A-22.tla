---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\* Finite version of the natural numbers used for model checking.
\* The configuration will replace the standard Nat with NatOverride.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* Aliases to expose the identifiers required by the .cfg file.
\* They are defined in the Boulanger module; we simply re‑export them.
\* ----------------------------------------------------------------------
Spec == Boulanger!Spec
Init == Boulanger!Init
Next == Boulanger!Next

MutualExclusion == Boulanger!MutualExclusion
TypeOK           == Boulanger!TypeOK
Inv              == Boulanger!Inv

\* ----------------------------------------------------------------------
\* Optional helper invariant that can be used as a state constraint
\* (the .cfg file will refer to it as a state constraint, not an invariant).
\* ----------------------------------------------------------------------
TicketBoundOK == \A i \in 1..N : tickets[i] < MaxNat

====