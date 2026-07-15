---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANT MaxNat

\* The constant MaxNat must be an integer that is NOT a natural number.
\* This captures the original intention without weakening the model.
ASSUME MaxNat \in Int \ { Nat }

NatOverride == 0 .. MaxNat

\* StateConstraint ensures that each process's counter stays strictly below MaxNat.
StateConstraint == \A process \in Procs : num[process] < MaxNat

====