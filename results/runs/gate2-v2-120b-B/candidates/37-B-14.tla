---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers
VARIABLE smokers, dealer

(* 'Offers' is a subset of subsets of Ingredients, each missing exactly one ingredient *)
ASSUME /\ Offers \subseteq SUBSET Ingredients
       /\ \A o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1

(* Types *)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

(* Helper to choose the unique smoking smoker *)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(* Initial state *)
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(* The dealer puts an offer on the table and the smoker who has the missing ingredient starts smoking *)
startSmoking ==
    /\ dealer /= {}
    /\ \E r \in Ingredients :
          /\ r \notin dealer                \* r is the missing ingredient
          /\ smokers'[r].smoking = TRUE
          /\ \A i \in Ingredients :
                (i = r) => smokers'[i].smoking = TRUE
                (i # r) => smokers'[i].smoking = FALSE
    /\ dealer' = {}

(* The smoker finishes, the table is cleared, and the dealer selects a new offer *)
stopSmoking ==
    /\ dealer = {}
    /\ \E r \in Ingredients :
          /\ smokers[r].smoking = TRUE
          /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
    /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(* Invariant: at most one smoker is smoking at any time *)
AtMostOne == Cardinality({ r \in Ingredients : smokers[r].smoking }) <= 1

====