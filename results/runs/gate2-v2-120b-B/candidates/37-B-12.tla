---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers

VARIABLES smokers, dealer

(* Type correctness *)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}

(* Helper to choose a unique element satisfying a predicate *)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(* Initial state: all smokers not smoking, dealer holds an arbitrary offer *)
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(* When there is an offer, the unique smoker whose ingredient is missing
   starts smoking; the dealer becomes empty. *)
startSmoking == /\ dealer /= {}
                /\ \E r \in Ingredients :
                      /\ r \notin dealer
                      /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
                      /\ dealer' = {}

(* When the dealer is empty, the smoking smoker stops and the dealer
   receives a new offer. *)
stopSmoking == /\ dealer = {}
               /\ \E r \in Ingredients :
                     /\ smokers[r].smoking
                     /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
                     /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_<<smokers, dealer>>
FairSpec == Spec /\ WF_<<smokers, dealer>>(Next)

(* At most one smoker may be smoking at any instant *)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

====