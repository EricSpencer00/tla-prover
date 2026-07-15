---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers

VARIABLES smokers, dealer

TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}

ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

startSmoking ==
  /\ dealer /= {}
  /\ LET missing == Ingredients \ dealer IN
     /\ smokers' = [r \in Ingredients |-> [smoking |-> IF r \in missing THEN TRUE ELSE smokers[r].smoking]]
     /\ dealer' = {}

stopSmoking ==
  /\ dealer = {}
  /\ LET r == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking) IN
     /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
     /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next, vars)

AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

====