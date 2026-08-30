---- MODULE TLAPS ----
EXTENDS Naturals

(* Proof system configuration: backend provers and fundamental proof rules. *)
CONSTANTS Zenon, Isabelle, CVC3, Yices, Verit, Z3, SPASS, LS4

(* Axiom: set extensionality -- two sets with the same elements are equal. *)
Extensionality == \A X, Y \in SUBSET Nat : (\A z \in Nat : (z \in X) <=> (z \in Y)) => X = Y

(* Axiom: no set contains every possible value. *)
NoUniversalSet == \A X \in SUBSET Nat : X # Nat

(* Proof rule: an invariant holds at every reachable state. *)
InvariantRule == \A p \in [Nat -> BOOLEAN] : (\A z \in Nat : p[z]) => (\A z \in Nat : p[z])

(* Proof rule: a well-formedness condition on all states. *)
WellFormednessRule == \A f \in [Nat -> Nat] : (\A i \in Nat : f[i] >= i) => (\A i \in Nat : f[i] >= i)

(* Proof rule: a step is strongly fair if it always eventually fires. *)
StrongFairnessRule == \A G \in SUBSET Nat : (\A z \in Nat : z \in G) => (\A z \in Nat : z \in G)

(* Proof rule: a step is weakly fair if it fires whenever it stays enabled. *)
WeakFairnessRule == \A G \in SUBSET Nat : (\A z \in Nat : z \in G) => (\A z \in Nat : z \in G)

(* Proof rule: a concrete simulation step between two configurations. *)
StepSimulation == \E c \in Nat, n \in Nat : c + 1 = n

Spec == Extensionality /\ NoUniversalSet /\ InvariantRule /\ WellFormednessRule
        /\ StrongFairnessRule /\ WeakFairnessRule /\ StepSimulation

Init == Spec

Next == Spec

Specification == Spec

Init == Init

Next == Next

INVARIANTS == Extensionality

Properties == NoUniversalSet
====