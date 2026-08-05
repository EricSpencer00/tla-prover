---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, VeriT, Z3, Spass, LS4,
  Timeout, Tactic

ZenonP == [tool |-> Zenon, timeout |-> Timeout]
IsabelleP == [tool |-> Isabelle, timeout |-> Timeout]
CVC3P == [tool |-> CVC3, timeout |-> Timeout]
YicesP == [tool |-> Yices, timeout |-> Timeout]
VeriTP == [tool |-> VeriT, timeout |-> Timeout]
Z3P == [tool |-> Z3, timeout |-> Timeout]
SpassP == [tool |-> Spass, timeout |-> Timeout]
LS4P == [tool |-> LS4, tactic |-> Tactic]

ASSUME LS4P.tactic \in {"auto", "inv"}

SetExtensionality ==
  \A x, y \in SUBSET (Nat \times Nat) : (x = y) <=> (\A a \in x : a \in y)

NoSetContainsAll ==
  \A x \in SUBSET (Nat \times Nat) : \E a \notin x : TRUE

====