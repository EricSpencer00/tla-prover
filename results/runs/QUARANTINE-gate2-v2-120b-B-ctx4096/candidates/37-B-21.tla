-------------------------- MODULE CigaretteSmokers --------------------------
(***************************************************************************)
(* A specification of the cigarette smokers problem, originally            *)
(* described in 1971 by Suhas Patil.                                       *)
(* https://en.wikipedia.org/wiki/Cigarette_smokers_problem                 *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers
VARIABLE smokers, dealer

(***************************************************************************)
(* 'Ingredients' is a set of ingredients, originally                       *)
(* {matches, paper, tobacco}. 'Offers' is a subset of subsets of           *)
(* ingredients, each missing just one ingredient                           *)
(***************************************************************************)
ASSUME /\ Offers \subseteq SUBSET Ingredients
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

(***************************************************************************)
(* 'smokers' is a function from the ingredient the smoker has              *)
(* infinite supply of, to a BOOLEAN flag signifying smoker's state         *)
(* (smoking/not smoking)                                                   *)
(* 'dealer' is an element of 'Offers', or an empty set                     *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(***************************************************************************)
(* startSmoking: the dealer places an offer (a set missing one ingredient) *)
(* and the smoker who possesses the missing ingredient begins smoking.     *)
(* The missing ingredient is exactly the one not present in the offer.    *)
(* The dealer then becomes empty, indicating the offer has been taken.    *)
(***************************************************************************)
startSmoking ==
  /\ dealer /= {}
  /\ LET missing == Ingredients \ dealer
     IN /\ Cardinality(missing) = 1
        /\ \E r \in missing :
              /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
        /\ dealer' = {}

(***************************************************************************)
(* stopSmoking: when the dealer is empty, the currently smoking smoker   *)
(* finishes smoking and the dealer selects a new offer.                    *)
(***************************************************************************)
stopSmoking ==
  /\ dealer = {}
  /\ LET r == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking)
     IN /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
        /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* An invariant checking that at most one smoker smokes at any particular  *)
(* moment.                                                                 *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1
=============================================================================