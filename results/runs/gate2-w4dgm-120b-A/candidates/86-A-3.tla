---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4, Nil, Halt, MaxWait

Pragmas == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

\* A backend is invoked with a fixed time budget, then marked halted.
Spend(b) == IF b = Nil THEN Nil ELSE b[1] - 1

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

VARIABLES elapsed, dispatch, halted

vars == <<elapsed, dispatch, halted>>

TypeOK ==
  /\ elapsed \in [Pragmas -> Nat]
  /\ dispatch \in 0..Cardinality(Pragmas)
  /\ halted \in 0..Cardinality(Pragmas)

Init ==
  /\ elapsed = [p \in Pragmas |-> MaxWait]
  /\ dispatch = 0
  /\ halted = 0

\* A backend runs while it has budget left; running out marks it halted.
Run(p) ==
  /\ p \notin halted
  /\ elapsed[p] > 0
  /\ elapsed' = [elapsed EXCEPT ![p] = Spend(@)]
  /\ UNCHANGED <<dispatch, halted>>

Halt(p) ==
  /\ p \notin halted
  /\ elapsed[p] = 0
  /\ halted' = halted \cup {p}
  /\ UNCHANGED <<elapsed, dispatch>>

Release(p) ==
  /\ p \notin halted
  /\ halted' = halted \cup {p}
  /\ UNCHANGED <<elapsed, dispatch>>

Dispatch(p) ==
  /\ p \notin halted
  /\ dispatch' = dispatch + 1
  /\ UNCHANGED <<elapsed, halted>>

Steady == UNCHANGED vars

Next ==
  \/ \E p \in Pragmas : Run(p) \/ Halt(p) \/ Release(p) \/ Dispatch(p)
  \/ Steady

Spec == Init /\ [][Next]_vars

BudgetConserved == SumOver(elapsed, Pragmas) + dispatch + Cardinality(halted) = Cardinality(Pragmas) * MaxWait

SetExtensionality ==
  \A A, B \in SUBSET Pragmas : (\A x \in Pragmas : (x \in A) <=> (x \in B)) => A = B

NoSetContainsEveryValue == \A A \in SUBSET Pragmas : A # Pragmas

\* These are core TLAPS rules from Lamport's paper; their names are reserved.
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

Specification == Spec
INIT == Init
NEXT == Next
INVARIANTS == {BudgetConserved}
PROPERTIES == {SetExtensionality, NoSetContainsEveryValue}
====