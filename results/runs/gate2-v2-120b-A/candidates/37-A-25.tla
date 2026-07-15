---- MODULE CigaretteSmokers ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANT Ingredients          \* set of all ingredients (e.g., {"matches","paper","tobacco"})
CONSTANT Offers               \* set of subsets, each missing exactly one ingredient

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
AllIngredients == Ingredients
AllOffers      == Offers

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES smokers, offer

(* smokers is a function mapping each ingredient to a Boolean indicating
   whether the smoker who owns that ingredient is currently smoking. *)
(* offer is either a subset of Ingredients (the current offer) or the
   special value "Smoking" indicating that a smoker is currently smoking. *)

(*--------------------------------------------------------------------
  Type invariant (for sanity checking)
--------------------------------------------------------------------*)
TypeOK ==
    /\ smokers \in [Ingredients -> BOOLEAN]
    /\ (offer \in AllOffers) \/ (offer = "Smoking")

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
FullSet == Ingredients

SmokingSmoker == 
    \E i \in Ingredients : smokers[i] = TRUE

CurrentSmokingIngredient == 
    CHOOSE i \in Ingredients : smokers[i] = TRUE

Smokable(i) == 
    /\ smokers[i] = FALSE
    /\ offer # "Smoking"
    /\ (FullSet \ {i}) = offer

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ smokers = [i \in Ingredients |-> FALSE]
    /\ offer \in AllOffers

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
StartSmoking ==
    /\ \E i \in Ingredients : Smokable(i)
    /\ LET i == CHOOSE j \in Ingredients : Smokable(j) IN
          /\ smokers' = [smokers EXCEPT ![i] = TRUE]
          /\ offer'   = "Smoking"

StopSmoking ==
    /\ offer = "Smoking"
    /\ \E i \in Ingredients : smokers[i] = TRUE
    /\ LET i == CurrentSmokingIngredient IN
          /\ smokers' = [smokers EXCEPT ![i] = FALSE]
          /\ offer'   = CHOOSE o \in AllOffers

Next == \/ StartSmoking \/ StopSmoking

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == 
    Init /\ [][Next]_<<smokers, offer>>

(*--------------------------------------------------------------------
  Invariant: At most one smoker is smoking
--------------------------------------------------------------------*)
AtMostOne == Cardinality({ i \in Ingredients : smokers[i] = TRUE }) <= 1

(*--------------------------------------------------------------------
  THEOREMS (optional, but keep module tidy)
--------------------------------------------------------------------*)
THEOREM Spec => []TypeOK
THEOREM Spec => []AtMostOne

====