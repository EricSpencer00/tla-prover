---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Ingredients, Offers

VARIABLES smokers, offer

(*-----------------------------------------------------------------
  Variables:
    smokers : [ingredients -> BOOLEAN]
      Mapping each ingredient to a boolean indicating whether the
      smoker that owns that ingredient is currently smoking.
    offer   : SUBSET Ingredients
      The current set of ingredients placed on the table.  It is
      either a valid offer (missing exactly one ingredient) or
      the empty set, which signals that a smoker is currently
      smoking.
-----------------------------------------------------------------*)

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
AllIngredients == Ingredients

(* A valid offer must be a subset of Ingredients missing exactly
   one ingredient. *)
IsValidOffer(s) == s \in Offers

(* The set of smokers currently smoking *)
CurrentSmokers == { i \in Ingredients : smokers[i] }

(* The set of smokers that could smoke given the current offer *)
EligibleSmokers == { i \in Ingredients :
                     ~smokers[i] /\ IsValidOffer(offer) /\ offer = { j \in Ingredients : j # i } }

(*-----------------------------------------------------------------
  Type correctness predicate (optional but useful)
-----------------------------------------------------------------*)
TypeOK ==
    /\ smokers \in [Ingredients -> BOOLEAN]
    /\ offer \in SUBSET Ingredients

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ smokers = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
StartSmoking ==
    /\ offer # {}
    /\ /\ \E i \in EligibleSmokers :
          /\ smokers' = [smokers EXCEPT ![i] = TRUE]
          /\ offer'   = {}
    /\ UNCHANGED << >>

StopSmoking ==
    /\ offer = {}
    /\ /\ \E i \in Ingredients :
          /\ smokers[i] = TRUE
          /\ smokers' = [smokers EXCEPT ![i] = FALSE]
    /\ /\ offer' \in Offers
    /\ UNCHANGED << >>

Next ==
    \/ StartSmoking
    \/ StopSmoking

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<smokers, offer>>

(*-----------------------------------------------------------------
  Safety invariant: at most one smoker is smoking at any time
-----------------------------------------------------------------*)
AtMostOne == Cardinality(CurrentSmokers) <= 1

(*-----------------------------------------------------------------
  Theorem (optional) that Spec implies the safety invariant
-----------------------------------------------------------------*)
THEOREM Spec => []AtMostOne

====