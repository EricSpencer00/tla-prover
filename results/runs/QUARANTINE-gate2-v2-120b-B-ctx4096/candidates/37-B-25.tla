---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers

VARIABLE smokers, dealer

(* Types *)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}

(* Initial predicate *)
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(* Helper to pick the unique smoking smoker *)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(* startSmoking: dealer provides the missing ingredient *)
startSmoking == 
    /\ dealer /= {}
    /\ LET missing == Ingredients \cup dealer \ {r \in Ingredients : r \in dealer}
       IN /\ missing \in Ingredients
          /\ smokers' = [smokers EXCEPT ![missing].smoking = TRUE]
    /\ dealer' = {}

(* stopSmoking: the smoker that is currently smoking finishes *)
stopSmoking ==
    /\ dealer = {}
    /\ \E r \in Ingredients : smokers[r].smoking
    /\ LET r == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking)
       IN /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
          /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_<<smokers, dealer>>

AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

=============================================================================