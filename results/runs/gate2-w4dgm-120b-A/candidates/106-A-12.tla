---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
  MAXV

VARIABLES
  x

vars == <<x>>

Bounded == x <= MAXV

TypeOK ==
  /\ x \in 0..MAXV

Spec ==
  /\ Bounded
  /\ Bounded' = Bounded
====