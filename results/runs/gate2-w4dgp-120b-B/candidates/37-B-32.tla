---- MODULE CigaretteSmokers
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers
VARIABLE smokers, dealer

ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

\* A smoker starts smoking iff the table has a complete set of ingredients.
\* The smoker who starts is the one whose private supply, together
\* with the table, gives a full set.
startSmoking ==
  /\ dealer # {}
  /\ smokers' = [r \in Ingredients |->
                   [smoking |-> {r} \cup dealer = Ingredients]]
  /\ dealer' = {}

\* When nobody is on the table, one smoking smoker returns to the ready state.
stopSmoking ==
  /\ dealer = {}
  /\ LET r == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking)
     IN smokers' = [smokers EXCEPT ![r].smoking = FALSE]
  /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

\* At most one smoker smokes at any particular moment.
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1
====