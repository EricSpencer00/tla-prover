---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

(*--------------------------------------------------------------------
  CONSTANTS
--------------------------------------------------------------------*)
CONSTANTS Ingredients, Offers

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES smokers, offer

(*--------------------------------------------------------------------
  Derived definitions
--------------------------------------------------------------------*)
(* The set of all possible offers is given by the constant Offers. *)
AllOffers == Offers

(* Each smoker is identified by the ingredient they have in infinite supply. *)
Smokers == Ingredients

(* A smoker is currently smoking iff its entry in the mapping is TRUE. *)
Smoking(s) == smokers[s]

(* The set of smokers that are currently smoking *)
CurrentSmoking == { s \in Smokers : Smoking(s) }

(*--------------------------------------------------------------------
  Type invariant (helps TLC catch type errors)
--------------------------------------------------------------------*)
TypeOK ==
    /\ smokers \in [Smokers -> BOOLEAN]
    /\ offer \in AllOffers \cup { {} }

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ smokers = [s \in Smokers |-> FALSE]
    /\ offer \in AllOffers

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
StartSmoking ==
    /\ offer # {}                     \* dealer has placed an offer
    /\ \E s \in Smokers :
          /\ offer = Ingredients \ {s}   \* the missing ingredient is s
          /\ smokers' = [smokers EXCEPT ![s] = TRUE]
    /\ offer' = {}                    \* table cleared while smoking

StopSmoking ==
    /\ offer = {}                     \* a smoker is currently smoking
    /\ \E s \in Smokers :
          /\ smokers[s] = TRUE
          /\ smokers' = [smokers EXCEPT ![s] = FALSE]
    /\ offer' \in AllOffers

Next ==
    \/ StartSmoking
    \/ StopSmoking

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<smokers, offer>>

(*--------------------------------------------------------------------
  Safety invariant: at most one smoker is smoking at any time
--------------------------------------------------------------------*)
AtMostOne == Cardinality(CurrentSmoking) <= 1

=============================================================================