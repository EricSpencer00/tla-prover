---- MODULE TLAPS ----
EXTENDS Naturals, TLC

CONSTANT UNIV

VARIABLE x

Init == x = FALSE
Next == x' = ~x

INIT == Init
NEXT == Next
SPECIFICATION == Init /\ [][Next]_<<x>>

INVARIANTS == {}
PROPERTIES == {}

(* Backend provers *)
Zenon(p) == p
Isabelle(p) == p
CVC3(p) == p
Yices(p) == p
veriT(p) == p
Z3(p) == p
SPASS(p) == p
LS4(p) == p

(* Foundational theorems *)
THEOREM SetExtensionality ==
  ASSUME S, T \in SUBSET UNIV,
         \A x \in UNIV: (x \in S) <=> (x \in T)
  PROVE  S = T

THEOREM NoSetContainsAll ==
  ASSUME S \in SUBSET UNIV
  PROVE \E x \in UNIV: x \notin S

(* Temporal logic proof rules *)
Invariance(P) == P
WellFormedness(P) == P
StrongFairness(P) == P
WeakFairness(P) == P
StepSimulation(P) == P

====