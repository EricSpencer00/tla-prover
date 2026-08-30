---- MODULE TLAPS ----
EXTENDS Naturals

(* Backends: prover dispatchers for the TLA Proof System (TLAPS). *)
\* Each of these is a primitive the proof system expands into a concrete
\* call to the named prover with its timeout/tactic.
Decl(decl) == decl
Zenon(in) == zenon[in]
Isabelle(in) == isabelle[in]
CVC3(in) == cvc3[in]
Yices(in) == yices[in]
VeriT(in) == verit[in]
Z3(in) == z3[in]
SPASS(in) == spass[in]
LS4(in) == ls4[in]

(* Temporal-logic proof rules from Lamport's TLA+ paper.  They are named
\* here so later proofs can invoke them by name; the rules themselves do
\* not change the system state. *)
Invariance(f) == f
WellFormed(p) == p
StrongFairness(p) == p
WeakFairness(p) == p
StutterStep == TRUE

Constant == "Constant"
SpecConstant == "SpecConstant"

(* The module is a library of definitions, so the system it configures has
\* a trivial state and no system-level actions. *)
VARIABLES dummy
vars == << dummy >>

Init == dummy = 0

Spec == Init

TypeOK == dummy \in 0..0

SetExtensionality ==
  \A a, b \in SUBSET {SpecConstant, Constant} :
    (\A x \in {SpecConstant, Constant} : x \in a <=> x \in b) => a = b

NoUniversalSet == \A x \in {SpecConstant, Constant} : x \notin {SpecConstant, Constant}

Spec == Spec /\ TypeOK /\ SetExtensionality /\ NoUniversalSet
====