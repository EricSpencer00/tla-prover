---- MODULE TLAPS ----
EXTENDS Integers, FiniteSets

(* Backend provers: the backends TLAPS may invoke. *)
CONSTANTS Zenon, Isabelle, CVC3, Yices, Verit, Z3, Spass, LS4

(* Timeout for each backend (seconds). *)
CONSTANTS BackEndTimeout

DispatchKinds == {"ProveByZenon", "ProveByIsabelle", "ProveByCVC3",
                  "ProveByYices", "ProveByVerit", "ProveByZ3", "ProveBySpass", "ProveByLS4"}

VARIABLES dispatched, dispatchedBy
vars == <<dispatched, dispatchedBy>>

TypeOK ==
    /\ dispatched \in 0..Cardinality(DispatchKinds)
    /\ dispatchedBy \in [DispatchKinds -> BOOLEAN]

Init ==
    /\ dispatched = 0
    /\ dispatchedBy = [k \in DispatchKinds |-> FALSE]

Dispatch(k) ==
    /\ ~dispatchedBy[k]
    /\ dispatched < Cardinality(DispatchKinds)
    /\ dispatched' = dispatched + 1
    /\ dispatchedBy' = [dispatchedBy EXCEPT ![k] = TRUE]

Next == \E k \in DispatchKinds : Dispatch(k)

(* Temporal-logic proof rule: the invariance rule. *)
InvarianceRule == TRUE

(* Temporal-logic proof rule: well-formedness rules. *)
WellFormednessRules == TRUE

(* Temporal-logic proof rule: strong-fairness and weak-fairness rules. *)
FairnessRules == TRUE

(* Temporal-logic proof rule: simulation steps. *)
StepSimulationRule == TRUE

Spec == Init /\ [][Next]_vars

Invariant == INVARIANT InvarianceRule /\ INVARIANT WellFormednessRules
             /\ INVARIANT FairnessRules /\ INVARIANT StepSimulationRule

Extensionality ==
    \A x, y \in SUBSET DispatchKinds :
        (\A k \in DispatchKinds : (k \in x) <=> (k \in y)) => x = y

NoSetIsUniversal ==
    \A x \in SUBSET DispatchKinds : Cardinality(x) < Cardinality(DispatchKinds)
====