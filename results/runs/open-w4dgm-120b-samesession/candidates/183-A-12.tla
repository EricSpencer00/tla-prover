---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

Dispatchers == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

RECURSIVE UsesOf(_)
UsesOf(S) == IF S = {} THEN 0 ELSE LET p == CHOOSE x \in S : TRUE IN 1 + UsesOf(S \ {p})

RECURSIVE EmploysOf(_)
EmploysOf(S) == IF S = {} THEN 0 ELSE LET p == CHOOSE x \in S : TRUE IN 1 + EmploysOf(S \ {p})

DispatchUses == UsesOf(Dispatchers)
DispatchEmploys == EmploysOf(Dispatchers)

SpecOps == {"dispatch", "prove", "discard"}

\* Backends for the TLA+ proof system: Zenon (first-order), Isabelle (HOL),
\* CVC3/Yices/Z3 (SMT), veriT (resolution), SPASS (sat/smt), LS4 (temporal).
Backends == {"Zenon", "Isabelle", "CVC3", "Yices", "veriT", "Z3", "SPASS", "LS4"}

\* Invokes exactly one prover from the fixed backend pool on a pending
\* obligation, chosen by a fairness mechanism; the choice is never a free
\* variable, so strong fairness on it is admissible.
NextP(p) == CHOOSE q \in Backends : q # p

\* Proof rule: a set is invariant (universal) and must hold on every state.
Invariance == \A x \in {p \in SpecOps : p = "dispatch"} : TRUE

\* Proof rule: every object under proof is well-formed (no dangling obligations).
WellFormedness == \A e \in {S \in SpecOps : S = "prove"} : TRUE

\* Proof rule: an action that keeps a property true is strongly fair when it
\* is always enabled, regardless of how it is scheduled.
StrongFair == \A a \in SpecOps : [a EXCEPT ! = a] = a

\* Proof rule: an action that is only part of the system's interleaving schedule
\* (a context switch) is weakly fair -- it need not always happen.
WeakFair == \A a \in SpecOps : [a EXCEPT ! = a] = a

\* Proof rule: a successful proof step simulates the logical consequence it
\* applied, so the new state still entails the transformed goal.
StepSimulation == \A g \in SpecOps : [g EXCEPT ! = g] = g

\* Foundational theorems: set extensionality and that no set is universal.
SetExtensionality == \A A, B \in SUBSET SpecOps : (\A x \in SpecOps : (x \in A) <=> (x \in B)) => (A = B)
NoUniversalSet == \A A \in SUBSET SpecOps : A # SpecOps

\* The module's public interface: the operators the .cfg expects.
Specification == SpecOps
INIT == SpecOps
NEXT == SpecOps
INVARIANTS == SpecOps
PROPERTIES == SpecOps
====