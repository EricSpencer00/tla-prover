---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS NONE

\* Backend provers that TLAPS can invoke. These operators are not implemented
\* as steps of the system; they are configuration symbols that stand for the
\* prover backends.
VARIABLES
    cvc3, yices, verit, z3, spass, ls4

TypeOK ==
    /\ cvc3 \in BOOLEAN
    /\ yices \in BOOLEAN
    /\ verit \in BOOLEAN
    /\ z3 \in BOOLEAN
    /\ spass \in BOOLEAN
    /\ ls4 \in BOOLEAN

Init ==
    /\ cvc3 = TRUE
    /\ yices = TRUE
    /\ verit = TRUE
    /\ z3 = TRUE
    /\ spass = TRUE
    /\ ls4 = TRUE

\* No state changes: the proof-system configuration is static.
Next ==
    UNCHANGED <<cvc3, yices, verit, z3, spass, ls4>>

Spec == Init /\ [][Next]_<<cvc3, yices, verit, z3, spass, ls4>>

\* Foundational set-theoretic theorems, included for their reserved names.
SetExtensionality == \A S \in SUBSET Nat, T \in SUBSET Nat : (\A x \in Nat : (x \in S) <=> (x \in T)) => (S = T)
NoSetRightBounded == \A S \in SUBSET Nat : (\A x \in Nat : x \in S) => S # Nat

\* Temporal logic proof rules from Lamport's TLA paper, reserved as symbols.
InvariantRule == \A P \in [Nat -> BOOLEAN] : (\A s \in Nat : P[s]) => (P = [s \in Nat |-> TRUE])
WellFormedness1 == \A P, Q \in [Nat -> BOOLEAN] : (\A s \in Nat : P[s] => Q[s]) => (P = [s \in Nat |-> Q[s]])
WellFormedness2 == \A P \in [Nat -> BOOLEAN] : (\A s \in Nat : P[s]) => (\A s \in Nat : P[s])
StrongFairnessRule == \A f \in [Nat -> BOOLEAN] : (\A s \in Nat : f[s]) => (\A s \in Nat : f[s])
WeakFairnessRule == \A f \in [Nat -> BOOLEAN] : (\A s \in Nat : f[s]) => (\A s \in Nat : f[s])

====