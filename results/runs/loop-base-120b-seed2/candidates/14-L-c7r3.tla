---- MODULE MCBoulanger ----
EXTENDS Naturals

(* Constants required by the original Boulanger specification *)
CONSTANT N, MaxNat
CONSTANT num, previous, max, pc, unchecked, nxt, flag

(* Finite replacement for the infinite set of natural numbers *)
NatOverride == 0 .. MaxNat

(* Instantiate the original Boulanger specification, mapping the constant N *)
INSTANCE Boulanger WITH N <- N

(* State constraint: all ticket numbers stay strictly below MaxNat *)
StateConstraint == \A i \in 1 .. N : Boulanger!ticket[i] < MaxNat

====