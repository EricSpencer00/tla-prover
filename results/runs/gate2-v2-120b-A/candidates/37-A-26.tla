----MODULE CigaretteSmokers----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANT Ingredients
CONSTANT Offers

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
AllIngredients == Ingredients

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES SmokerAt, Offer

(*-----------------------------------------------------------------
  Types (for TypeOK invariant)
-----------------------------------------------------------------*)
SmokerAtType == SmokerAt \in [Ingredients -> BOOLEAN]
OfferType   == Offer \in SUBSET Ingredients

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
AllSmokingFalse == \A i \in Ingredients : ~ SmokerAt[i]

IsValidOffer(o) == 
    /\ o \in Offers
    /\ Cardinality(o) = Cardinality(Ingredients) - 1
    /\ \A i \in Ingredients : i \notin o => TRUE   \* (implicitly true)

BlankOffer == {}

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ SmokerAt = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : 
          /\ IsValidOffer(o)
          /\ Offer = o

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
StartSmoking ==
    /\ Offer # BlankOffer
    /\ \E i \in Ingredients :
          /\ Offer = Ingredients \ {i}
          /\ ~ SmokerAt[i]
          /\ SmokerAt' = [SmokerAt EXCEPT ![i] = TRUE]
    /\ Offer' = BlankOffer

StopSmoking ==
    /\ Offer = BlankOffer
    /\ \E i \in Ingredients :
          /\ SmokerAt[i] = TRUE
          /\ SmokerAt' = [SmokerAt EXCEPT ![i] = FALSE]
    /\ \E o \in Offers :
          /\ IsValidOffer(o)
          /\ Offer' = o

Next ==
    \/ StartSmoking
    \/ StopSmoking

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<SmokerAt, Offer>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeOK == SmokerAtType /\ OfferType

AtMostOne == 
    Cardinality({ i \in Ingredients : SmokerAt[i] }) <= 1

(*-----------------------------------------------------------------
  Liveness (optional, but defined for completeness)
-----------------------------------------------------------------*)
WeakFairness == WF_<<SmokerAt, Offer>>(Next)

=============================================================================