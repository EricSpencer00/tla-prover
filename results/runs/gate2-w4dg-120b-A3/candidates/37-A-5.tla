---- MODULE CigaretteSmokers ----
EXTENDS Integers

CONSTANTS Ingredients, Offers

\* SmokingNow maps the holder of each ingredient to whether that smoker is
\* currently smoking; Offer is the dealer's currently posted offer, or empty
\* (a smoking session in progress) while someone smokes.
VARIABLES SmokingNow, Offer

vars == <<SmokingNow, Offer>>

TypeOK ==
  /\ SmokingNow \in [Ingredients -> BOOLEAN]
  /\ Offer \subseteq Ingredients

\* At most one smoker smokes: the set of currently-smoking ingredients has
\* size 0 or 1.
AtMostOne ==
  Cardinality({i \in Ingredients : SmokingNow[i]}) <= 1

Init ==
  /\ SmokingNow = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : Offer = o

\* StartSmoking fires only while no one smokes; it clears the offer, so a smoker
\* can only be smoking while Offer = {}, which enforces mutual exclusion.
StartSmoking ==
  /\ Offer # {}
  /\ \E i \in Ingredients :
       /\ ~SmokingNow[i]
       /\ Offer \cup {i} = Ingredients
       /\ SmokingNow' = [SmokingNow EXCEPT ![i] = TRUE]
  /\ Offer' = {}

StopSmoking ==
  /\ Offer = {}
  /\ \E i \in Ingredients :
       /\ SmokingNow[i]
       /\ SmokingNow' = [SmokingNow EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : Offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)

====