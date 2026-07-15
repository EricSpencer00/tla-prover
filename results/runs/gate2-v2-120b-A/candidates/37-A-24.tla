---- MODULE CigaretteSmokers ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES
    smoking,   \* mapping from each ingredient to the smoker's smoking status (TRUE if that smoker is currently smoking)
    offer      \* the current offer on the table; either a subset of Ingredients missing exactly one ingredient, or {} when a smoker is smoking

(* ------------------------------------------------------------------------- *)
(*  Derived definitions                                                       *)
(* ------------------------------------------------------------------------- *)

AllIngredients == Ingredients

\* The set of all valid offers (subsets missing exactly one ingredient)
ValidOffers == { s \in SUBSET Ingredients : Cardinality(s) = Cardinality(Ingredients) - 1 }

\* Consistency check: Offers must be a subset of the valid offers
TypeOK == /\ Ingredients # {}
          /\ Offers \subseteq ValidOffers
          /\ smoking \in [Ingredients -> BOOLEAN]
          /\ offer \in SUBSET Ingredients

\* At most one smoker is smoking
AtMostOne == Cardinality({ i \in Ingredients : smoking[i] }) <= 1

\* Initially, no smoker is smoking and the dealer places a nondeterministic valid offer
Init == /\ smoking = [i \in Ingredients |-> FALSE]
        /\ offer \in Offers

\* Action: a smoker whose own ingredient completes the full set begins smoking
StartSmoking == 
    /\ offer # {}
    /\ \E i \in Ingredients :
          /\ (ingredient i is the missing one) /\ 
          /\ ~smoking[i] 
          /\ offer = Ingredients \ {i}
          /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

\* Action: the currently smoking smoker stops and the dealer places a new offer
StopSmoking == 
    /\ offer = {}
    /\ \E i \in Ingredients :
          /\ smoking[i]
          /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ offer' \in Offers

\* Next-state relation
Next == \/ StartSmoking
        \/ StopSmoking

\* Temporal specification
Spec == Init /\ [][Next]_<<smoking, offer>>

=============================================================================