---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokers, dealer

(* Type invariant *)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}

(* Helper to choose the unique smoking smoker *)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(* Initial state *)
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(* When the dealer offers a set, the smoker who has the missing ingredient starts smoking. *)
startSmoking == 
    /\ dealer # {}
    /\ \E missing \in Ingredients :
          /\ dealer = Ingredients \ {missing}
          /\ smokers' = [smokers EXCEPT ![missing].smoking = TRUE]
          /\ dealer' = {}

(* When no offer is present, a smoking smoker finishes and the dealer picks a new offer. *)
stopSmoking == 
    /\ dealer = {}
    /\ \E s \in Ingredients :
          /\ smokers[s].smoking = TRUE
          /\ smokers' = [smokers EXCEPT ![s].smoking = FALSE]
          /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_<<smokers, dealer>>

(* Optional: WF fairness, not required for safety *)
FairSpec == Spec /\ WF_<<smokers, dealer>>(Next)

(* Invariant: at most one smoker smokes at any moment *)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

====