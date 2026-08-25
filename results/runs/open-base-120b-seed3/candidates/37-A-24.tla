---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES smoker, offer

(*--------------------------------------------------------------------
  Definitions
--------------------------------------------------------------------*)

\* The set of all variables for the action
vars == << smoker, offer >>

\* Type invariant
TypeOK ==
    /\ smoker \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \/ offer = {}

\* At most one smoker is smoking
AtMostOne ==
    \A i, j \in Ingredients :
        (smoker[i] /\ smoker[j]) => i = j

\* Initial state: nobody is smoking and the dealer places a nondeterministic
\* valid offer.
Init ==
    /\ smoker = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\* Helper: the ingredient missing from the current offer (if any)
MissingIngredient(off) ==
    LET missing == Ingredients \ off IN
        IF Cardinality(missing) = 1 THEN CHOOSE i \in missing : TRUE ELSE NULL

\* Action: a smoker starts smoking
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
          /\ offer = Ingredients \ {i}
          /\ smoker' = [j \in Ingredients |-> IF j = i THEN TRUE ELSE FALSE]
          /\ offer' = {}
    /\ UNCHANGED << >>   \* no other variables

\* Action: the currently smoking smoker stops and a new offer is placed
StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients : smoker[i] = TRUE
    /\ smoker' = [j \in Ingredients |-> FALSE]
    /\ offer' \in Offers
    /\ UNCHANGED << >>   \* no other variables

Next ==
    StartSmoking \/ StopSmoking

\* Weak fairness for progress
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================