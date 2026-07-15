---- MODULE TLAPS ----
EXTENDS SETS, TLC

(* Backend provers *)
Zenon(p) == p
Isabelle(p) == p
CVC3(p) == p
Yices(p) == p
veriT(p) == p
Z3(p) == p
SPASS(p) == p
LS4(p) == p

(* Temporal logic proof rules *)
Invariance(p) == p
WellFormedness(p) == p
StrongFairness(p) == p
WeakFairness(p) == p
StepSimulation(p) == p

THEOREM SetExtensionality ==
    \A s, t \in SUBSET UNIV :
        (\A x \in UNIV : (x \in s) <=> (x \in t)) => s = t

THEOREM NoUniversalSet ==
    \A s \in SUBSET UNIV : \E x \in UNIV : x \notin s

====