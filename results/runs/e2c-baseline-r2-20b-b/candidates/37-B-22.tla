---- MODULE CigaretteSmokers
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers
VARIABLE smokers, dealer

(* The following assumptions describe the structure of the sets *)
ASSUME
  /\ Offers \subseteq (SUBSET Ingredients)
  /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

(* Type checking for the state variables *)
TypeOK ==
  /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
  /\ dealer \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

(* Helper function - not used in the corrected specification but kept for reference *)
ChooseOne(S, P(_)) ==
  CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init ==
  /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
  /\ dealer \in Offers

(* The correct startSmoking action assigns the smoker with the missing
   ingredient to smoke and empties the dealer's offer. *)
startSmoking ==
  /\ dealer /= {}
  /\ LET r == CHOOSE x \in Ingredients : x \notin dealer IN
       smokers' = [smokers EXCEPT ![r].smoking = TRUE]
  /\ dealer' = {}

(* Stop smoking: the smoker who is currently smoking stops and the dealer
   may offer a new set of ingredients. *)
stopSmoking ==
  /\ dealer = {}
  /\ LET r == ChooseOne(Ingredients,
             LAMBDA x : smokers[x].smoking)
       IN smokers' = [smokers EXCEPT ![r].smoking = FALSE]
  /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(* Invariant: at most one smoker smokes at any given time *)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1
=============================================================================