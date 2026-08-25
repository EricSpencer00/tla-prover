---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

\* -----------------------------------------------------------------
\* Finite override for the infinite set Nat (used only for model checking)
\* -----------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* -----------------------------------------------------------------
\* Aliases to the definitions provided by the Boulanger specification
\* -----------------------------------------------------------------
Init == Boulanger!Init
Next == Boulanger!Next
Vars == Boulanger!Vars

\* -----------------------------------------------------------------
\* State constraint: all ticket numbers must stay strictly below MaxNat
\* -----------------------------------------------------------------
StateConstraint == \A i \in 1 .. N : ticket[i] < MaxNat

\* -----------------------------------------------------------------
\* The full specification (behavioural) used by TLC
\* -----------------------------------------------------------------
Spec == Init /\ [] (StateConstraint /\ [Next]_Vars)

\* -----------------------------------------------------------------
\* Invariants exported for the .cfg file
\* -----------------------------------------------------------------
MutualExclusion == Boulanger!MutualExclusion
TypeOK          == Boulanger!TypeOK
Inv             == Boulanger!Inv

=============================================================================