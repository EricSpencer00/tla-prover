---- MODULE CigaretteSmokers ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Ingredients, Offers

\* A mapping from each ingredient to the smoking status of the smoker who holds it
Smoking == [i \in Ingredients |-> FALSE]

\* The current offer on the table: either a non‑empty subset of Ingredients missing exactly one ingredient,
\* or the empty set (meaning a smoker is currently smoking)
VARIABLES smoking, offer

\* The set of all valid offers (subsets missing exactly one ingredient)
ValidOffers == { S \in SUBSET Ingredients : Cardinality(S) = Cardinality(Ingredients) - 1 }

\* Type invariant ensuring variables stay within their intended domains
TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in ({ } \cup ValidOffers)

\* Safety invariant: at most one smoker is smoking at any moment
AtMostOne ==
  Cardinality({ i \in Ingredients : smoking[i] }) <= 1

\* Initial state: no smoker is smoking, and the dealer places a nondeterministic valid offer
Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ offer \in ValidOffers

\* Helper: the unique ingredient that is missing from the current offer
Missing(offer) ==
  CHOOSE ing \in Ingredients : ing \notin offer

\* Action: a smoker whose own ingredient completes the full set starts smoking
StartSmoking ==
  /\ offer # {}
  /\ \E sm \in Ingredients :
        /\ sm = Missing(offer)               \* this smoker has the missing ingredient
        /\ smoking' = [smoking EXCEPT ![sm] = TRUE]
        /\ offer' = {}
  /\ UNCHANGED Ingredients

\* Action: the currently smoking smoker stops and the dealer places a new offer
StopSmoking ==
  /\ offer = {}
  /\ \E sm \in Ingredients :
        /\ smoking[sm]                     \* the smoker who is currently smoking
        /\ smoking' = [smoking EXCEPT ![sm] = FALSE]
        /\ offer' \in ValidOffers
  /\ UNCHANGED Ingredients

Next ==
  \/ StartSmoking
  \/ StopSmoking

\* Full specification
Spec ==
  Init /\ [][Next]_<<smoking, offer>>

\* Exported names
THEOREM Spec => []TypeOK
THEOREM Spec => []AtMostOne

====