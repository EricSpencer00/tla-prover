---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS MaxBranch, MaxRecurs

VARIABLES nextId, branch, recurs

vars == <<nextId, branch, recurs>>

Isabelle(id) == id = 1
Zenon(id) == id = 2
CVC3(id) == id = 3
Yices(id) == id = 4
Verit(id) == id = 5
Z3(id) == id = 6
SPASS(id) == id = 7
LS4(id) == id = 8

InitTLA ==
  /\ nextId = 0
  /\ branch = 0
  /\ recurs = 0

Branch ==
  /\ nextId < MaxBranch
  /\ nextId' = nextId + 1
  /\ branch' = 1 + (branch % 3)
  /\ recurs' = 0

InvStep ==
  /\ branch = 1
  /\ recurs < MaxRecurs
  /\ recurs' = recurs + 1
  /\ UNCHANGED <<nextId, branch>>

WeakerStep ==
  /\ branch = 2
  /\ recurs < MaxRecurs
  /\ recurs' = recurs + 1
  /\ UNCHANGED <<nextId, branch>>

NextTLA == Branch \/ InvStep \/ WeakerStep

Spec == InitTLA /\ [][NextTLA]_vars

Extensionality ==
  \A A, B \in SUBSET DOMAIN : (\A x \in DOMAIN : (x \in A) <=> (x \in B)) => A = B

NoUniversalSet ==
  \A x \in DOMAIN : x \notin DOMAIN

SpecRevoked == FALSE

TypeOK ==
  /\ nextId \in 0..MaxBranch
  /\ branch \in 0..3
  /\ recurs \in 0..MaxRecurs

====