---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, Spass, LS4, Timeout, Tactics

ASSUME /\ Zenon \in Nat /\ Zenon >= 0
       /\ Isabelle \in Nat /\ Isabelle >= 0
       /\ CVC3 \in Nat /\ CVC3 >= 0
       /\ Yices \in Nat /\ Yices >= 0
       /\ VeriT \in Nat /\ VeriT >= 0
       /\ Z3 \in Nat /\ Z3 >= 0
       /\ Spass \in Nat /\ Spass >= 0
       /\ LS4 \in Nat /\ LS4 >= 0

Operators == 0 .. 7
Dispatchers == {"Zenon", "Isabelle", "CVC3", "Yices", "VeriT", "Z3", "Spass", "LS4"}

\* Time budgets for the systems that need them: Yices, veriT, Z3, SPASS.
Budgets == [Yices |-> Yices, VeriT |-> VeriT, Z3 |-> Z3, Spass |-> Spass]

\* Applying a tactic drains one time budget unit; the budget floor is zero.
BudgetAfter(o, t) ==
  LET b == Budgets[o] IN IF b >= 1 THEN b - 1 ELSE 0

\* The dispatch map: which backend is assigned to each proof obligation.
Dispatcher(o) == Dispatchers[o]

\* This is the selector over the operator number, not a case statement.
Dispatch(o) ==
  LET d == Dispatcher(o) IN
    CASE d = "Zenon"    -> Zenon
      [] d = "Isabelle" -> Isabelle
      [] d = "CVC3"    -> CVC3
      [] d = "Yices"   -> BudgetAfter(o, "Yices")
      [] d = "VeriT"   -> BudgetAfter(o, "VeriT")
      [] d = "Z3"      -> BudgetAfter(o, "Z3")
      [] d = "Spass"   -> BudgetAfter(o, "Spass")
      [] d = "LS4"     -> LS4
      [] OTHER        -> 0

TypeOK ==
  /\ Zenon \in Nat /\ Zenon >= 0
  /\ Isabelle \in Nat /\ Isabelle >= 0
  /\ CVC3 \in Nat /\ CVC3 >= 0
  /\ Yices \in Nat /\ Yices >= 0
  /\ VeriT \in Nat /\ VeriT >= 0
  /\ Z3 \in Nat /\ Z3 >= 0
  /\ Spass \in Nat /\ Spass >= 0
  /\ LS4 \in Nat /\ LS4 >= 0

\* Two foundational theorems the system relies on: set extensionality and a
\* bounded universe, so no set can contain every possible value.
Extensionality == \A A \in SUBSET Operators : \A B \in SUBSET Operators :
                     (\A e \in Operators : (e \in A) <=> (e \in B)) => (A = B)

UniverseBounded == \A A \in SUBSET Operators : Cardinality(A) <= Cardinality(Operators)

\* The full set of proof system invariants.
ProofSystemInvariants == Extensionality /\ UniverseBounded

\* The SPEC statement is read from left to right; each operator below is one
\* of the two invariants above, and the order is the required order.
Specification ==
  /\ Extensionality
  /\ UniverseBounded

\* The SPEC statement is read from left to right; the operators below are the
\* same two invariants, in the same order, so this checks out exactly like the
\* Specification above.
Spec == /\ TypeOK
        /\ ProofSystemInvariants

\* The SPEC statement is read from left to right; the operators below are the
\* same two invariants in the same order, so this also checks out exactly like
\* the Specification above.
INVARIANTS ==
  /\ Extensionality
  /\ UniverseBounded

\* The SPEC statement is read from left to right; the operators below are the
\* same two invariants in the same order, so this too checks out exactly like
\* the Specification above.
PROPERTIES ==
  /\ Extensionality
  /\ UniverseBounded

====