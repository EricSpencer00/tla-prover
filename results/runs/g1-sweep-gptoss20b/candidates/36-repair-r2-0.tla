---- MODULE MCCheckpointCoordination ----
EXTENDS CheckpointCoordination, FiniteSets, Naturals, TLC

CONSTANTS MaxLog, MaxNat

MCNat == 0..MaxNat

MCLogIndex == 1..MaxLog

StateConstraint == OpenIndices /= {}

NodeSymmetry == Permutations(Node)

\* (Corrected) lease is held by the current leader
IncorrectlyOptimizedShouldReplaceLease(currentLease) ==
  ShouldReplaceLease(currentLease)

=============================================================================