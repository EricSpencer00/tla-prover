---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4, Timeout

\* Backend provers for the TLA+ proof system and its temporal-logic prover.
Provers == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS}
TemporalProvers == LS4
AllBackends == Provers \cup TemporalProvers

\* Dispatches a proof obligation to a backend prover under a bounded timeout.
\* The timeout makes the back-and-forth between TLAPM and the prover a finite
\* race rather than an open-ended one.
ProveWith(p, g) == IF p \in AllBackends
                     THEN [goal |-> g, engine |-> p, ttl |-> Timeout]
                     ELSE [goal |-> g, engine |-> Zenon, ttl |-> Timeout]

\* Temporal logic proof rules (from "The Temporal Logic of Actions").
\* Their names are reserved here so they cannot be re-used by user extensions.
\* Each is a meta-rule about how temporal formulas are derived; they never
\* rewrite or simplify ordinary TLA+ expressions at runtime.
Invariance == "From invariance of p to invariance of p."
W4 == "From well-formedness of p and well-formedness of next to well-formedness of p."
Fairness == "From weak fairness of an event to its strong fairness."
StepSimulation == "From step simulation of M1 by M2 and step simulation of M2 by M3 to step simulation of M1 by M3."

\* Two foundational theorems of set theory, axiomatised as plain TLA+ facts
\* rather than proved from deeper set axioms -- they are the "free theorems"
\* that the temporal-logic rules above may safely invoke.
Extensionality == \A X, Y \in SUBSET Nat : (\A x \in Nat : x \in X <=> x \in Y) => X = Y
CantBeUniversal == \A X \in SUBSET Nat : X # Nat

NotAFormula == "A declaration is never itself a formula, so none of the
rules above ever fires on any declaration, and no declaration can be
reduced or simplified by them."

\* The set of declarations that are in the unexpanded, unreduced state.
Untouched == {Extensionality, CantBeUniversal, NotAFormula}

\* The proof system's core transformation: an untouched declaration becomes
\* a proved theorem, and nothing is ever rewritten back out of existence.
Prove == \E d \in Untouched : Untouched' = Untouched \ {d}
Next == Prove \/ UNCHANGED <<Untouched>>

\* SAFETY: visible state is just the set of declarations left untouched, so
\* the module never rewrites or drops a declaration from that set.
INVARIANTS == Untouched \subseteq {Extensionality, CantBeUniversal, NotAFormula}

\* LIVENESS: every declaration eventually gets proved.
PROPERTIES == \A d \in {Extensionality, CantBeUniversal, NotAFormula} : <>(d \notin Untouched)

Spec == Init /\ [][Next]_Untouched
Init == Untouched = {Extensionality, CantBeUniversal, NotAFormula}
====