---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Ingredients, \* Set of all ingredients (e.g., {"matches","paper","tobacco"})
    Offers      \* Set of all valid offers, each missing exactly one ingredient

VARIABLES
    smoking,   \* [ingredient -> BOOLEAN] indicates if the smoker that owns the ingredient is currently smoking
    currentOffer   \* either a subset of Ingredients (the dealer's offer) or {} when a smoker is smoking

(* Helper definition: the complete set of ingredients *)
AllIngredients == Ingredients

(* Type invariant (helps TLC but not the safety property) *)
TypeOK == 
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ currentOffer \in SUBSET Ingredients

(* Initial state: no smoker is smoking, dealer places a nondeterministic valid offer *)
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ currentOffer \in Offers

(* Action: a smoker whose ingredient completes the set begins smoking *)
StartSmoking ==
    /\ currentOffer # {}
    /\ \E i \in Ingredients :
          /\ i \notin currentOffer               \* the missing ingredient belongs to this smoker
          /\ smoking[i] = FALSE
          /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ currentOffer' = {}

(* Action: the currently smoking smoker stops and dealer places a new offer *)
StopSmoking ==
    /\ currentOffer = {}
    /\ \E i \in Ingredients :
          /\ smoking[i] = TRUE
          /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ currentOffer' \in Offers

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_<<smoking, currentOffer>>

(* Safety invariant: at most one smoker is smoking at any time *)
AtMostOne == Cardinality({ i \in Ingredients : smoking[i] = TRUE }) <= 1

====