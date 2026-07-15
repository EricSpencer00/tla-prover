---- MODULE MCBoulanger ------------------------------
EXTENDS Boulanger
CONSTANT MaxNat

\* The original specification incorrectly used a set difference
\* to define NatOverride.  The intention is to model the natural
\* numbers up to MaxNat (inclusive) when MaxNat is itself a natural
\* number.  We therefore require MaxNat to be a natural number and
\* define NatOverride as the interval 0..MaxNat.  This preserves the
\* intended semantics while allowing the model to satisfy the
\* assumption that NatOverride is a subset of Nat.
ASSUME MaxNat \in Nat
NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat
=============================================================================