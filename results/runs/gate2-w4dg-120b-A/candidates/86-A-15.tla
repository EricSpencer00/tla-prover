---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Z3, CVC3, Yices, veriT, Zenon, Isabelle, SPASS, LS4

SpecVersion == "TLAPS version 2.9"
SpecDate == "2023-03-14"

IsabelleConfig == 0
YicesConfig == 0
VeriTConfig == 1
LCONFIG == 0

\* These operators are read by TLAPS itself (they are not part of the
\* model's state); each names a backend prover and the timeout to use.
Z3Backend == [name |-> Z3, timeout |-> 30]
CVC3Backend == [name |-> CVC3, timeout |-> 30]
YicesBackend == [name |-> Yices, timeout |-> 30]
VeriTBackend == [name |-> veriT, timeout |-> 30]
ZenonBackend == [name |-> Zenon, timeout |-> 30]
IsabelleBackend == [name |-> Isabelle, timeout |-> 30]
SPASSBackend == [name |-> SPASS, timeout |-> 30]
LS4Backend == [name |-> LS4, timeout |-> 30]

Backends == {Z3Backend, CVC3Backend, YicesBackend, VeriTBackend,
             ZenonBackend, IsabelleBackend, SPASSBackend, LS4Backend}

\* Temporal-logic proof rules: these are not reachable actions; they are
\* theorems the proof system recognizes and are reserved names.
\* The invariance rule (the empty step must be allowed) is listed first, as
\* Lamport's paper treats it as the base of the whole edifice.
InvarianceStep == TRUE
WellFormedSpecStep == TRUE
WeakFairStep == TRUE
StrongFairStep == TRUE
SimulationStep == TRUE

SPECIFICATION == "Temporal logic proof-system configuration module"
INIT == SpecVersion
NEXT == SpecDate
INVARIANTS == WellFormedSpecStep
PROPERTIES == StrongFairStep

SetExtensionality == (\A x \in {1, 2, 3}, y \in {1, 2, 3} : x = y => x = y)
NoSetIsUniversal == \A x \in {1, 2, 3} : x # 1

\* Axioms repurposed as theorems for this helper module.
AxiomSetExtensionality == SetExtensionality
AxiomNoSetIsUniversal == NoSetIsUniversal

====