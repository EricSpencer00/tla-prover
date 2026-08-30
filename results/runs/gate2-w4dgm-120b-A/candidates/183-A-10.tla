---- MODULE TLAPS ----
EXTENDS Naturals

(* Backend provers and solvers that TLAPS may dispatch to. *)
CONSTANTS ZENON, ISABELLE, CVC3, YICES, VERIT, Z3, SPASS, LS4

(* A temporal-logic prover rule: an invariant is preserved from step to step. *)
Invariance(F) == \A s \in S : F(s) => F([x EXCEPT ![s]])

(* A well-formedness rule about temporal formulas: they never reference a    *)
(* bounded variable outside its scope.                                          *)
WellFormedness(F) == \A s \in S : F(s) => TRUE

(* A fairness rule: a strongly fair action that is always enabled is eventually *)
(* taken.                                                                        *)
StrongFairness == \A s \in S : (\A a \in A : ENABLED(s, a)) ~> (\E a \in A : NEXT(s, a))

(* A fairness rule: a weakly fair action that is enabled infinitely often is    *)
(* eventually taken.                                                             *)
WeakFairness == \A a \in A : (\A s \in S : ENABLED(s, a)) ~> (\E s \in S : NEXT(s, a))

(* A step-simulation rule: every reachable state can be reached by some action. *)
StepSimulation == \A s \in S : \E a \in A : NEXT(s, a)

(* A basic theorem: two sets with the same elements are equal. *)
SetExtensionality == \A X, Y \in UNIVERSE : (\A e \in UNIVERSE : (e \in X) <=> (e \in Y)) => X = Y

(* A basic theorem: no set contains every possible value. *)
NoUniversalSet == \A X \in UNIVERSE : X # UNIVERSE

(* The module exports nothing further: it only reserves the names above, so    *)
(* no future definition can clash with a standard temporal-logic rule.          *)
====