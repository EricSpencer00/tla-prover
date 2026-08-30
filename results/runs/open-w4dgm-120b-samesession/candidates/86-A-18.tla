-------------------------- MODULE TLAPS --------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
  zenonProxy, zenonTimeout, iz3Proxy, iz3Timeout,
  laTeX, spassProxy, evm, spassTimeout

Spec == "Spec"
Init == "Init"
Step == "Step"
Induction == "Induction"
OrElse == "OrElse"

IsabelleTLA == "IsabelleTLA"
Yices == "Yices"
Z3SMT == "Z3SMT"
CVC3SMT == "CVC3SMT"
VeriT == "VeriT"
Zenon == "Zenon"
SPASS == "SPASS"
LS4 == "LS4"

SANY == "SANY"
TLA == "TLA"
PDFLATEX == "PDFLATEX"
TEX == "TEX"
DVI2PDF == "DVI2PDF"

MODULES == {"ls4", "sany", "tla"}
PROVER == {"isabelle", "yices", "z3", "cvc3", "verit", "ls4"}
BACKEND == {IsabelleTLA, Yices, Z3SMT, CVC3SMT, VeriT, LS4}
SMT == {Yices, Z3SMT, CVC3SMT, VeriT}
LANGUAGE == "language"

VARIABLES level, action, obligation, subsequence, pending

vars == <<level, action, obligation, subsequence, pending>>

TypeOK ==
  /\ level \in {Spec, Init, Step, Induction, OrElse}
  /\ action \in {"tautology", "trivial", "trivialByHand" \/ Prover}
  /\ obligation \in 0..3
  /\ subsequence \in BOOLEAN
  /\ pending \in [Modules -> BOOLEAN]

Init ==
  /\ level = Spec
  /\ action = "tautology"
  /\ obligation = 0
  /\ subsequence = FALSE
  /\ pending = [m \in Modules |-> FALSE]

Next ==
  \/ \E m \in Modules :
       /\ pending' = [pending EXCEPT ![m] = TRUE]
       /\ UNCHANGED <<level, action, obligation, subsequence>>
  \/ \E p \in PROVER :
       /\ action' = p
       /\ pending' = [m \in Modules |-> FALSE]
       /\ UNCHANGED <<level, obligation, subsequence>>
  \/ \E n \in 0..3 :
       /\ level' = Step
       /\ action' = "trivial"
       /\ obligation' = n
       /\ subsequence' = (n % 2 = 0)
       /\ UNCHANGED <<pending>>

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(Next)

InductionRule ==
  /\ level = Spec
  /\ \A m \in Modules : pending[m]
  /\ level' = Init
  /\ UNCHANGED <<action, obligation, subsequence, pending>>

InvarianceRule ==
  /\ level = Init
  /\ action \in SMT
  /\ level' = Induction
  /\ UNCHANGED <<action, obligation, subsequence, pending>>

SimulationProved ==
  /\ level = Induction
  /\ action = LS4
  /\ level' = Step
  /\ UNCHANGED <<action, obligation, subsequence, pending>>

Stutter ==
  /\ level = Step
  /\ level' = Step
  /\ UNCHANGED <<action, obligation, subsequence, pending>>

NextStep ==
  \/ InductionRule \/ InvarianceRule \/ SimulationProved \/ Stutter

EveryObligationProved ==
  (level = Induction) ~> (level = Step)

Onward == NextStep

Extensionality ==
  \A A, B \in SUBSET Nat :
    (\A x \in Nat : (x \in A) <=> (x \in B)) => (A = B)

Undefinable == \A x \in Nat : ~(x \in Nat)

Theorems ==
  /\ Extensionality
  /\ Undefinable
  /\ EveryObligationProved
  /\ WF_vars(Onward)
=============================================================================