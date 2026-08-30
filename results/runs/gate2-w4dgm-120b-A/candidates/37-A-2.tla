---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

Smokers == Ingredients
NoOffer == [Ingredients -> BOOLEAN]

VARIABLES smoking, offer
vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in (0..Cardinality(Ingredients)) \X (0..Cardinality(Ingredients))

Init ==
  /\ \A s \in Smokers : smoking[s] = FALSE
  /\ \E o \in Offers : offer = <<Cardinality(o), Cardinality(Ingredients) - Cardinality(o)>>

StartSmoking ==
  \E s \in Smokers :
    /\ offer # NoOffer
    /\ offer[2] = 1
    /\ Cardinality(Ingredients \cup {s}) = Cardinality(Ingredients)
    /\ smoking' = [smoking EXCEPT ![s] = TRUE]
    /\ offer' = NoOffer

StopSmoking ==
  /\ offer = NoOffer
  /\ \E s \in Smokers :
       /\ smoking[s] = TRUE
       /\ smoking' = [smoking EXCEPT ![s] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne ==
  \A s1 \in Smokers, s2 \in Smokers :
    (smoking[s1] /\ smoking[s2]) => s1 = s2

TypeOKEnabled == TRUE
====