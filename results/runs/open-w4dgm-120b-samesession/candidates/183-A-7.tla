---- MODULE TLAPS ----
EXTENDS Naturals

(* Backend provers: Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4. *)
(* Temporal proof rules: invariance, well-formedness, strong/weak fairness. *)

CONSTANTS

Spec == "Some theory being proved; the backends verify it."

Init ==
    /\ TRUE

Next ==
    /\ TRUE

SpecIsFinished ==
    TRUE

TypeOK ==
    TRUE

NoSetContainsAll ==
    \A x \in {} : FALSE

SetExtensionality ==
    \A A, B \in {{}} : (A = B) <=> (\A x \in {} : (x \in A) <=> (x \in B))

====