---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Ingredients, Offers

(* --algorithm placeholder (none needed) *)

VARIABLES Smoking, Offer

\* Smoking maps each ingredient to a Boolean indicating if its owner is smoking
\* Offer is the current set of ingredients placed on the table (empty when a smoker is smoking)

(* Helper definitions *)
AllIngredients == Ingredients

SmokerCanSmoke(i) == 
    /\ Smoking[i] = FALSE
    /\ i \in (AllIngredients \ Offer)   \* i is the missing ingredient

AtMostOne == 
    /\ Cardinality({ i \in AllIngredients : Smoking[i] }) <= 1

TypeOK == 
    /\ Smoking \in [AllIngredients -> BOOLEAN]
    /\ Offer \in (Offers \cup {{} })

(* Initial state: no one smoking, Offer chosen nondeterministically from Offers *)
Init == 
    /\ Offer \in Offers
    /\ \A i \in AllIngredients : Smoking[i] = FALSE

(* Action: a smoker whose missing ingredient matches the offer starts smoking *)
StartSmoking == 
    /\ Offer # {}
    /\ \E i \in AllIngredients :
          /\ SmokerCanSmoke(i)
          /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
    /\ Offer' = {}

(* Action: the currently smoking smoker stops and dealer places a new offer *)
StopSmoking == 
    /\ Offer = {}
    /\ \E i \in AllIngredients :
          /\ Smoking[i] = TRUE
          /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
    /\ Offer' \in Offers

Next == 
    \/ StartSmoking
    \/ StopSmoking

Spec == Init /\ [][Next]_<<Smoking, Offer>>

=============================================================================