---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets, TLC

CONSTANTS Ingredients, Offers

(* ----------------------------------------------------------------------
   Valid offers are subsets that miss exactly one ingredient
   ---------------------------------------------------------------------- *)
ValidOffer == { o \in SUBSET Ingredients :
                  Cardinality(o) = Cardinality(Ingredients) - 1 }

(* Basic assumptions on the constants *)
ASSUME Ingredients # {}
ASSUME Offers \subseteq ValidOffer

VARIABLES smoker, offer

vars == <<smoker, offer>>

(* ----------------------------------------------------------------------
   Initialization: no smoker is smoking, dealer places a nondeterministic
   initial offer
   ---------------------------------------------------------------------- *)
Init ==
  /\ smoker = [i \in Ingredients |-> FALSE]
  /\ offer   \in Offers

(* Helper: the ingredient that is missing from the current offer *)
MissingIngredient(offer) == Ingredients \ offer

(* ----------------------------------------------------------------------
   StartSmoking: dealer's offer is present, the unique smoker whose
   ingredient completes the set begins to smoke, and the offer is cleared
   ---------------------------------------------------------------------- *)
StartSmoking ==
  /\ offer # {}
  /\ /\ Cardinality(offer) = Cardinality(Ingredients) - 1
     /\ Cardinality(MissingIngredient(offer)) = 1
  /\ LET i == CHOOSE x \in MissingIngredient(offer) : TRUE IN
        /\ smoker[i] = FALSE
        /\ smoker' = [smoker EXCEPT ![i] = TRUE]
        /\ offer'   = {}

(* ----------------------------------------------------------------------
   StopSmoking: the smoker that is currently smoking stops, and a new
   offer is placed
   ---------------------------------------------------------------------- *)
StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
        /\ smoker[i] = TRUE
        /\ smoker' = [smoker EXCEPT ![i] = FALSE]
        /\ offer'   \in Offers

Next ==
  \/ StartSmoking
  \/ StopSmoking

(* ----------------------------------------------------------------------
   Specification with weak fairness
   ---------------------------------------------------------------------- *)
Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ smoker \in [Ingredients -> BOOLEAN]
  /\ offer   \in SUBSET Ingredients

(* ----------------------------------------------------------------------
   Safety: at most one smoker is smoking
   ---------------------------------------------------------------------- *)
AtMostOne ==
  Cardinality({ i \in Ingredients : smoker[i] }) <= 1

====