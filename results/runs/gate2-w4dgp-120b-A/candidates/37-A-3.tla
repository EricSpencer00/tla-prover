---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

ASSUME Offers \subseteq SUBSET Ingredients

\* Each valid offer is missing exactly one ingredient from the complete set of
\* ingredients the dealer could use.
ASSUME \A o \in Offers : \E i \in Ingredients : o = Ingredients \ {i}

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

AtMostOne ==
  \A i \in Ingredients : \A j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

\* The dealer places an initial offer on the table.
Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

\* The dealer offers a non-empty set; exactly one smoker, whose own ingredient
\* completes the full set, begins smoking and the offer is cleared.
StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ ~smoking[i]
       /\ offer \cup {i} = Ingredients
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

\* When the offer is empty a smoking action is in progress; the smoker stops
\* and the dealer places a new offer.
StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
       /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

\* With no further fairness condition the system would be free to loop forever
\* with a smoker going and coming back at its own leisure.
SpecWF == Spec /\ WF_vars(Next)

====