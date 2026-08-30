---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

\* Backend provers: each is a configuration record for the TLAPS service.
\* The rules below (from Lamport's TLA+ paper) are included only to reserve
\* their names; this module itself neither applies nor checks them.
CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

Pragma == [name: {"zenon", "isabelle", "cvc3", "yices", "verit", "z3",
                  "spass", "ls4"},
           timeout: 0..3, tactic: {"auto", "force", "none"}]

Backends == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

\* A Zenon-timeout configuration; others are analogous.
ZenonT(t) == [name |-> "zenon", timeout |-> t, tactic |-> "auto"]

TypeOK == /\ Backends \subseteq Pragma
          /\ \A b \in Backends : b.name \in {"zenon", "isabelle", "cvc3",
                                             "yices", "verit", "z3",
                                             "spass", "ls4"}
          /\ \A b \in Backends : b.timeout \in 0..3
          /\ \A b \in Backends : b.tactic \in {"auto", "force", "none"}

\* Invariance rule (reserved name).
InvariantRule == TRUE

\* Well-formedness rule (reserved name).
WellFormedRule == TRUE

\* Strong fairness rule (reserved name).
StrongFairRule == TRUE

\* Weak fairness rule (reserved name).
WeakFairRule == TRUE

\* Step simulation rule (reserved name).
StepSimulationRule == TRUE

Extensionality == \A X, Y \in SUBSET Nat :
                    (\A x \in X : x \in Y) /\ (\A y \in Y : y \in X) => X = Y

SetNotUniversal == \A X \in SUBSET Nat : X # Nat

Spec == /\ TypeOK
        /\ Extensionality
        /\ SetNotUniversal
        /\ Init
        /\ Next
====