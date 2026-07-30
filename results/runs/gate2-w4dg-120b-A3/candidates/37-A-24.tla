---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer
vars == <<smoking, offer>>

\* smoking[i] is the smoking status of the smoker holding an infinite
\* supply of ingredient i. offer is the current dealer's offer, or empty
\* (meaning a smoker is currently smoking and the table is cleared).
TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

\* At most one smoker is actively smoking: the set of currently-smoking
\* smokers never has size > 1. (Specification requires this as an explicit invariant.)
AtMostOne == Cardinality({i \in Ingredients : smoking[i]}) <= 1

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

\* An offer that is non-empty names the offered ingredients; the single smoker
\* who can smoke is the one whose own ingredient fills the missing piece.
StartSmoking(i) ==
  /\ offer # {}
  /\ ~smoking[i]
  /\ (offer \cup {i}) = Ingredients
  /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

\* The only action that re-fills the offer; it fires once per smoking episode.
StopSmoking(i) ==
  /\ offer = {}
  /\ smoking[i]
  /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next ==
  \/ \E i \in Ingredients : StartSmoking(i)
  \/ \E i \in Ingredients : StopSmoking(i)

\* A weak fairness condition over the next-state relation guarantees progress:
\* the system never settles into a state where no further action ever fires.
Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)

====