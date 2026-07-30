---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Zenon
  Isabelle
  CVC3
  Yices
  Verit
  Z3
  SPASS
  LS4

VARIABLES clock

vars == clock

TypeOK ==
  /\ clock \in 0..2

Init ==
  /\ clock = 0

Tick ==
  /\ clock < 2
  /\ clock' = clock + 1

Roll ==
  /\ clock = 2
  /\ clock' = 0

Next ==
  \/ Tick
  \/ Roll

Spec == Init /\ [][Next]_vars

Extensionality ==
  \A A, B \in SUBSET {0, 1, 2} : (\A x \in {0, 1, 2} : (x \in A) = (x \in B)) => (A = B)

CantContainAll ==
  \A A \in SUBSET {0, 1, 2} : ~(\A x \in {0, 1, 2} : x \in A)

====