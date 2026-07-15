---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(*=================================================================
  TLAPS: Configuration infrastructure for the TLA+ Proof System.
  It declares operators that refer to backend provers and
  states fundamental logical theorems used by the proof system.
  No state variables, actions, or explicit temporal behavior are
  modeled here; the module only reserves identifiers for later
  use.
=================================================================