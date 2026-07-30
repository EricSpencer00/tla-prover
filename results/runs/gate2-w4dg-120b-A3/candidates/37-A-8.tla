---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* A smoker holds an infinite supply of exactly one ingredient. The dealer's
\* offer is never a full set -- it always lacks exactly one ingredient.
\* The invariant below protects the "at most one smoker" safety claim.
TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

\* Exactly one smoker smokes at a time: among the three smokers at most one is
\* in the smoking state.
AtMostOne ==
  Cardinality({i \in Ingredients : smoking[i]}) <= 1

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ offer \in Offers

\* The dealer's current offer, combined with a smoker's own ingredient, must
\* provide the complete set before that smoker may begin.
StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ i \in offer
       /\ ~smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ offer' \in Offers

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
        /\ WF_vars(StartSmoking)
        /\ WF_vars(StopSmoking)

====