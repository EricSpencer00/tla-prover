---- MODULE CigaretteSmokers
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers
VARIABLE smokers, dealer

ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

\* The smoker who owns the missing ingredient has an infinite supply of it,
\* and the coalition of the other two can only ever support one missing ingredient,
\* so at most one smoker can ever be smoking.
StartSmoking == /\ dealer /= {}
                /\ \E r \in Ingredients, n \in Offers :
                     /\ {r} \cup n = Ingredients
                     /\ dealer = n
                     /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
                     /\ dealer' = {}
                \/ /\ dealer = {}
                     /\ \A r \in Ingredients : smokers' = [smokers EXCEPT ![r].smoking = FALSE]
                     /\ dealer' = {}
                   

Next == StartSmoking

Spec == Init /\ [][Next]_vars

AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

====