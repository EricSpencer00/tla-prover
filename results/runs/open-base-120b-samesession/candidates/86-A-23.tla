---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

\* ********************************************************************
\* Backend provers for TLAPS.  These are only symbolic placeholders.
\* ********************************************************************

Zenon(expr, timeout) == 
  (* dispatch expr to the Zenon prover with given timeout *) 
  TRUE

Isabelle(expr, timeout) == 
  (* dispatch expr to the Isabelle prover with given timeout *) 
  TRUE

CVC3(expr, timeout) == 
  (* dispatch expr to the CVC3 prover with given timeout *) 
  TRUE

Yices(expr, timeout) == 
  (* dispatch expr to the Yices prover with given timeout *) 
  TRUE

VeriT(expr, timeout) == 
  (* dispatch expr to the veriT prover with given timeout *) 
  TRUE

Z3(expr, timeout) == 
  (* dispatch expr to the Z3 prover with given timeout *) 
  TRUE

SPASS(expr, timeout) == 
  (* dispatch expr to the SPASS prover with given timeout *) 
  TRUE

LS4(expr, timeout) == 
  (* dispatch expr to the LS4 temporal logic prover with given timeout *) 
  TRUE

\* ********************************************************************
\* Fundamental set-theoretic theorems
\* ********************************************************************

SetExtensionality == 
  \A A, B \in UNIV :
    (\A x \in UNIV : (x \in A) = (x \in B)) => A = B

NoUniversalSet == 
  \A S \in UNIV :
    ~(\A x \in UNIV : x \in S)

\* ********************************************************************
\* Temporal‑logic proof rules (names are reserved for future use)
\* ********************************************************************

\* Invariance rule:  from  Init /\ [] (Inv => [Next]_vars)  infer  []Inv
InvariantRule(Inv) == 
  Init /\ [] (Inv => [Next]_vars) => []Inv

\* Well‑formedness rule (Lamport's WF/SF definitions)
WellFormednessRule == 
  TRUE   \* placeholder – actual rule is defined in the standard library

\* Strong fairness rule (SF)
StrongFairness(SF) == 
  TRUE   \* placeholder

\* Weak fairness rule (WF)
WeakFairness(WF) == 
  TRUE   \* placeholder

\* Step simulation rule
StepSimulation == 
  TRUE   \* placeholder

\* ********************************************************************
\* Minimal state for the module (no real behaviour)
\* ********************************************************************

VARIABLES dummy

Init == dummy = 0

Next == UNCHANGED dummy

\* ********************************************************************
\* Required identifiers (even though the .cfg does not demand any)
\* ********************************************************************

SPECIFICATION == Init /\ [][Next]_<<dummy>>

INVARIANTS == {}

PROPERTIES == {}

====