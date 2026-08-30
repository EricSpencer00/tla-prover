---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, Verit, Z3, SPASS, LS4

Operators == {Zenon, Isabelle, CVC3, Yices, Verit, Z3, SPASS, LS4}

Assignment(k) == [Backend |-> k, Time |-> 0, Tactic |-> "default"]

RECURSIVE SumOver(_)
SumOver(S) ==
  IF S = {} THEN 0
  ELSE LET k == CHOOSE e \in S : TRUE IN Assignment(k).Time + SumOver(S \ {k})

SpecTotal == SumOver(Operators)

Spec == "TLA+ Proof System Backends"

Assignments == {Assignment(k) : k \in Operators}

InitValues == { [Backend |-> k, Time |-> 0, Tactic |-> "default"] : k \in Operators }

VARIABLES assignments
vars == <<assignments>>

TypeOK ==
  /\ assignments \subseteq Assignments
  /\ assignments # {}

Init == assignments = InitValues

Dispatch(k) ==
  /\ assignments' = {a \in assignments : a.Backend # k}
       \cup {Assignment(k)}
  /\ UNCHANGED <<>>

SetExtensionality ==
  \A X \in SUBSET Nat, Y \in SUBSET Nat :
    (\A e \in X : e \in Y) /\ (\A e \in Y : e \in X) => X = Y

NoSetCoversAll == \A X \in SUBSET Nat : X # Nat

Next ==
  \/ \E k \in Operators : Dispatch(k)
  \/ UNCHANGED vars

SpecState == Init /\ [][Next]_vars

InitConjecture == SpecState

SpecConjecture == SpecState

====