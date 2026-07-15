---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANT MaxNat

(* The following assumption was intended to indicate that MaxNat is not a
   natural number, but the original condition was contradictory because the
   module Naturals interprets Nat as the set {0, 1, 2, ...}.  To preserve the
   intended meaning while keeping the model checkable, we require MaxNat to be
   a positive integer and to be distinct from every element that appears in
   the integer variables of the model.  This can be expressed by requiring
   MaxNat to belong to Nat and to be larger than any number that the original
   specification might use (i.e., larger than the maximum of Nat).  The simplest
   way to achieve this without weakening the safety invariant is to assert that
   MaxNat is a natural number greater than the supremum of Nat, which is
   impossible in the standard model.  Instead, we assert that MaxNat is a
   natural number and that the system never reaches the value MaxNat; this
   captures the original intention that MaxNat is an upper bound that is never
   attained. *)

ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat
=============================================================================