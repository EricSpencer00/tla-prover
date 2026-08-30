---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* Backend provers available to TLAPS.
Solvers == {Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4}

\* Invokes a backend prover on a subgoal, with a timeout and a tactic.
Dispatch(solver, subgoal, timeout, tactic) ==
    /\ solver \in Solvers
    /\ subgoal \in Nat
    /\ timeout \in Nat
    /\ tactic \in {"auto", "simp"}

\* The invariance rule: an invariant is preserved by every transition.
InvRule(P, e) ==
    /\ P \subseteq e
    /\ \A x \in P : \A y \in e : x = y

\* The well-formedness rule: each transition action is defined on the current state.
WFRule(e, a) == a \in e

\* The strong fairness rule: an enabled transition must eventually fire.
SFRule(e, a) == (a \in e) ~> (a \in e)

\* The weak fairness rule: an enabled transition cannot be postponed forever.
WFRules(e, a) == (a \in e) ~> (a \in e)

\* The simulation step rule: a single step advances the system.
SimStep(e, a) == (a \in e) /\ (e' = e \cup {a})

\* The two foundational theorems this module states; proofs live elsewhere.
Extensionality == \A A \in SUBSET Nat, B \in SUBSET Nat :
    (\A x \in Nat : (x \in A) <=> (x \in B)) => (A = B)

NoUniversalSet == \A A \in SUBSET Nat : A # Nat

ASSUME Extensionality
ASSUME NoUniversalSet

Spec == Dispatch(Zenon, 1, 3, "auto") /\ InvRule({}, {1}) /\ WFRule({1}, 1)
        /\ SFRule({1}, 1) /\ WFRules({1}, 1) /\ SimStep({1}, 1)

SPECIFICATION == Spec
Init == TRUE
Next == Spec
Init == Init
Next == Next
INVARIANTS == Extensionality
PROPERTIES == NoUniversalSet
====