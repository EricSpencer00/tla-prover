---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  ONTOLOGY,
  ZENO,
  ISABELLE,
  YICES,
  CVC3,
  VERIT,
  SPASS,
  Z3,
  LS4,
  DEFAULT_TIMEOUT

INVARIANTS == {extensionality, noSetContainsAll}

PROPERTIES == {arithmetic, modAdd, xorLemma}
ASSUME arithmetic
ASSUME modAdd
ASSUME xorLemma

IsabelleSimp == "simp"
IsabelleAuto == "auto"
YicesSat == "sat"
LS4Valid == "valid"

Spec == TRUE
Init == TRUE
Next == TRUE

extensionality ==
  \A A, B \in SUBSET (1..2) : (\A x \in 1..2 : x \in A <=> x \in B) => A = B

noSetContainsAll ==
  \A S \in SUBSET (1..2) : (\A x \in 1..2 : x \in S) => S = {}

arithmetic == 2 * 2 = 4
modAdd == 0 + 1 - 1 = 0
xorLemma == TRUE

====