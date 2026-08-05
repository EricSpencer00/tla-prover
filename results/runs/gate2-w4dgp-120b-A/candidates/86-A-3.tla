---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS yicesTimeout, zsmtTimeout, spassTimeout

ASSUME yicesTimeout \in Nat /\ zsmtTimeout \in Nat /\ spassTimeout \in Nat

\* Backends: each tool is invoked with its command line and a per-run timeout.
\* The Zenon and Isabelle backends are hard-wired with their standard options.
\* The SMT backends (CVC3, Yices, veriT, Z3, LS4) all share the same timeout.
\* The SPASS backend has a separate timeout from the SMT ones.
\* The Smt module implements the IsSat operator used in the fairness rules below.
\* NOTE: this is a helper module from the standard proof library; the rules
\* are from Lamport's paper "The Temporal Logic of Actions".  They are included
\* so their names are reserved and cannot clash with future versions.

Zenon     == "zenon -tptp -pdt"
Isabelle  == "isabelle tptp"
Cvc3      == "cvc3 -t set"
Yices     == "yices -t " ^ yicesTimeout
VeriT     == "verit -t " ^ yicesTimeout
Z3        == "z3 -t " ^ zsmtTimeout
Lspass    == "Lspass -t " ^ spassTimeout
Spass     == "spass -t " ^ spassTimeout
Ls4       == "z3 -t " ^ zsmtTimeout

\* The invariance rule: an invariant of the step relation is an invariant of any
\* execution of it, and an invariant that is trivial in the initial state is
\* proved by its definition alone.
InvRule ==
  /\ \A s \in [State -> BOOLEAN] : (Init => s) /\ (\A x \in State : s' = s) => Inv
  /\ \A s \in [State -> BOOLEAN] :
       /\ (Init => s) /\ (\A x \in State : Step(x, x) => s' = s) => Inv

\* Set extensionality: two sets with the same elements are equal.
SetExtenConj == \A X, Y \in SUBSET Nat : (\A x \in Nat : x \in X <=> x \in Y) => X = Y

\* No set contains every possible value.
NoSetIsAll == \A X \in SUBSET Nat : X = Nat => FALSE

\* A step relation is well-formed when its nondeterministic choice can always be
\* decided by the SAT engine.
WFRule ==
  /\ \A Step \in [State -> SUBSET State] : (\A x \in State : IsSat(Step(x))) => WFStep

\* Strong fairness: a step that stays open forever is eventually taken.
SFRule ==
  /\ \A Step \in [State -> SUBSET State] : (\A x \in State : IsSat(Step(x))) => SFStep

\* Weak fairness: a step that is always open is eventually taken.
WFfRule ==
  /\ \A Step \in [State -> SUBSET State] : (\A x \in State : IsSat(Step(x))) => WFStep

\* Step simulation: a step that is always open but never taken is equivalent to
\* one that is both always open and always taken, which is an absurdity.
SstepRule ==
  /\ \A Step \in [State -> SUBSET State] : (\A x \in State : IsSat(Step(x))) => SStep

\* Every step defined by the system must be well-formed.
WFallsafe == \A Step \in [State -> SUBSET State] : WFRule

\* Every step subject to strong fairness must respect it.
SFallsafe == \A Step \in [State -> SUBSET State] : SFRule

\* Every step subject to weak fairness must respect it.
WFfallsafe == \A Step \in [State -> SUBSET State] : WFfRule

\* Every step defined by the system must respect step simulation.
Sstepallsafe == \A Step \in [State -> SUBSET State] : SstepRule

Spec == InvRule /\ WFallsafe /\ SFallsafe /\ WFfallsafe /\ Sstepallsafe

====