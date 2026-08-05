---- MODULE CigaretteSmokers
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers
VARIABLE smokers, dealer

ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

\* A smoker takes the dealer's ingredients and starts smoking only if the
\* dealer is holding a non-empty offer, atomically.
startSmoking == /\ dealer /= {}
                /\ smokers' = [r \in Ingredients |-> [smoking |-> {r} \cup dealer = Ingredients]]
                /\ dealer' = {}
                
\* When the current smoker finishes, the dealer is free to offer again.
stopSmoking == /\ dealer = {}
               /\ LET r == ChooseOne(Ingredients,
                                     LAMBDA x : smokers[x].smoking)
                  IN /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
                     /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1
====