---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

(* No state variables *)
VARIABLES

(* Initial condition *)
INIT == TRUE

(* Next-state relation: stuttering *)
NEXT == UNCHANGED {}

(* Specification *)
SPECIFICATION == INIT /\ [][NEXT]_<<>>

(* Invariants (empty set) *)
INVARIANTS == {}

(* Properties (empty set) *)
PROPERTIES == {}

(* Fundamental theorems *)

SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

NoUniversalSet ==
  ~(\E S \in SUBSET UNIV : UNIV \subseteq S)

(* Temporal logic proof rule placeholders *)

InvariantRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

====