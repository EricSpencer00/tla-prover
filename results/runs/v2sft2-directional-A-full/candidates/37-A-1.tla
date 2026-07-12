---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES Smokers, Offer

(* ---------------------------------------------------------------------- *)
(* Type correctness invariant (used by TLC to check the module's well-formedness) *)
TypeOK ==
    /\ Smokers \in [Ingredients -> BOOLEAN]
    /\ Offer \in SUBSET Ingredients
    /\ Offers \subseteq SUBSET Ingredients
    /\ \A i \in Ingredients : i \in Ingredients

(* ---------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ Smokers = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

(* ---------------------------------------------------------------------- *)
(* Actions *)
StartSmoking ==
    /\ Offer \in Offers
    /\ Offer # {}
    /\ LET i == CHOOSE x \in Ingredients \ Offer : TRUE IN
        /\ Smokers' = [Smokers EXCEPT ![i] = TRUE]
        /\ Offer'   = {}

StopSmoking ==
    /\ Offer = {}
    /\ \E i \in Ingredients : Smokers[i] = TRUE
    /\ LET i == CHOOSE x \in Ingredients : Smokers[x] = TRUE IN
        /\ Smokers' = [Smokers EXCEPT ![i] = FALSE]
        /\ Offer'   \in Offers

Next ==
    StartSmoking \/ StopSmoking

Spec ==
    Init /\ [][Next]_<<Smokers, Offer>>

(* ---------------------------------------------------------------------- *)
(* Safety invariant: at most one smoker is smoking at any moment *)
AtMostOne ==
    Cardinality({i \in Ingredients : Smokers[i] = TRUE}) <= 1

=============================================================================