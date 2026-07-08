---- MODULE CigaretteSmokers
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers
VARIABLE smokers, dealer

ASSUME
  /\ Offers \subseteq (SUBSET Ingredients)
  /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

startSmoking ==
  /\ dealer /= {}
  /\ LET r == CHOOSE x \in Ingredients : x \notin dealer
     IN  /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
         /\ dealer' = {}

stopSmoking ==
  /\ dealer = {}
  /\ LET r == CHOOSE x \in Ingredients : smokers[x].smoking
     IN smokers' = [smokers EXCEPT ![r].smoking = FALSE]
  /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1
=============================================================================