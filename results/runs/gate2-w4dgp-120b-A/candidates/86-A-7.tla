---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

\* Backend pragmas for TLAPS: these operators are no-ops at runtime; they
\* only inform the proof system which prover to invoke on a given obligation.
\* The name of each pragma must match the prover it addresses.
Zenon == "zenon"
Isabelle == "isabelle"
Cvc3 == "cvc3"
Yices == "yices"
Verit == "verit"
Z3 == "z3"
Spass == "spass"
LS4 == "ls4"

\* Foundational proof rules for temporal logic, from Lamport's TLA+ paper.
\* These are declared as operators so their names are reserved in the runtime
\* environment and cannot be re-used elsewhere in the system.
SetExtensionality == \A X, Y \in SUBSET Nat : (\A z \in Nat : z \in X <=> z \in Y) => X = Y
NoSetContainsAll == \A X \in SUBSET Nat : X = Nat => FALSE

=====