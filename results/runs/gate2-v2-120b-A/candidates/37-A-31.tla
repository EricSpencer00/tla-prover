---- MODULE CigaretteSmokers ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

(*--------------------------------------------------------------------
-- Type definitions
--------------------------------------------------------------------*)
\* The set of all possible values for the smoking mapping
SmokingSet == [i \in Ingredients |-> BOOLEAN]

(*--------------------------------------------------------------------
-- Helper definitions
--------------------------------------------------------------------*)
AllIngredients == Ingredients
FullSet == Ingredients

(* A valid offer is a subset of Ingredients that is missing exactly one
   ingredient; this is assumed to be captured by the constant set Offers. *)
ValidOffer(s) == s \in Offers

(*--------------------------------------------------------------------
-- Variables' meaning
--------------------------------------------------------------------*)
\* smoking[i] = TRUE iff the smoker that owns ingredient i is currently smoking.
\* offer   = {}  means a smoker is currently smoking.
\* offer   = a non‑empty subset of Ingredients (in Offers) means the dealer
            has placed that offer on the table.
\* At any instant at most one smoker may be smoking.

(*--------------------------------------------------------------------
-- Initial state
--------------------------------------------------------------------*)
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

(*--------------------------------------------------------------------
-- Actions
--------------------------------------------------------------------*)
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
          /\ i \notin offer               \* the missing ingredient
          /\ smoking[i] = FALSE
          /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
          /\ smoking[i] = TRUE
          /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ offer' \in Offers

Next ==
    \/ StartSmoking
    \/ StopSmoking

(*--------------------------------------------------------------------
-- Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<smoking, offer>>

(*--------------------------------------------------------------------
-- Invariants
--------------------------------------------------------------------*)
TypeOK ==
    /\ smoking \in SmokingSet
    /\ offer \in Offers \/ offer = {}

AtMostOne ==
    Cardinality({i \in Ingredients : smoking[i]}) <= 1

=============================================================================