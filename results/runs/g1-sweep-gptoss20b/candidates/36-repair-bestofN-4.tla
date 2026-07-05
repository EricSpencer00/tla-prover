---- MODULE MCCheckpointCoordination ----
EXTENDS CheckpointCoordination, FiniteSets, Naturals, TLC

CONSTANTS MaxLog, MaxNat

MCNat == 0..MaxNat

MCLogIndex == 1..MaxLog

StateConstraint == OpenIndices /= {}

NodeSymmetry == Permutations(Node)

IncorrectlyOptimizedShouldReplaceLease(currentLease) ==
  ShouldReplaceLease(currentLease) \/
  currentLease.node = Leader

====