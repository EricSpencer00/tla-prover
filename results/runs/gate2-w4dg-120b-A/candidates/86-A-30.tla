---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  MaxSteps, Unbounded

ASSUME MaxSteps \in Nat /\ Unbounded \in Nat

SpecStanzas == {"zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4"}

Zenon == [istp |-> TRUE, timeout |-> 0]

Isabelle == [istp |-> TRUE, tactic |-> "archive_reconstruct"]

Cvc3 == [istp |-> TRUE, timeout |-> 0]

Yices == [istp |-> TRUE, timeout |-> 0]

Verit == [istp |-> TRUE, timeout |-> 0]

Z3 == [istp |-> TRUE, timeout |-> 0]

Spass == [istp |-> TRUE, timeout |-> 0]

Ls4 == [istp |-> TRUE, mode |-> "LS4"]

Backends == {Zenon, Isabelle, Cvc3, Yices, Verit, Z3, Spass, Ls4}

Extensionality ==
  \A S \in (SUBSET (SUBSET UNIVERSE)), T \in (SUBSET (SUBSET UNIVERSE)) :
    (\A e \in UNIVERSE : (e \in S) <=> (e \in T)) => (S = T)

NoSetContainsAll == \A S \in (SUBSET (SUBSET UNIVERSE)) : UNIVERSE \notin S

UnfoldedQuantifier == \A e \in UNIVERSE : Cardinality({e}) = 1

TypeOK == Cardinality(UNIVERSE) = MaxSteps

Spec == SpecStanzas

Init == "zenon"

NextStep == "isabelle"

InvProp == "no set contains all values"

FairStep == "invariant holds"

Prop1 == Extensionality

Prop2 == NoSetContainsAll

====