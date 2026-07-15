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
       /\ \A o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1

(***************************************************************************)
(* 'smokers' is a function from the ingredient the smoker has              *)
(* infinite supply of, to a BOOLEAN flag signifying smoker's state         *)
(* (smoking/not smoking)                                                   *)
(* 'dealer' is an element of 'Offers', or the empty set                     *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init ==
  /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
  /\ dealer   = {}

(***************************************************************************)
(* The dealer chooses an offer (a set missing exactly one ingredient).    *)
(* The smoker who possesses the missing ingredient starts smoking.        *)
(***************************************************************************)
startSmoking ==
  /\ dealer = {}
  /\ dealer' \in Offers
  /\ \E missing \in Ingredients :
        /\ missing \notin dealer'
        /\ smokers' = [smokers EXCEPT ![missing].smoking = TRUE]

(***************************************************************************)
(* The currently smoking smoker stops, and the dealer clears its offer.    *)
(***************************************************************************)
stopSmoking ==
  /\ dealer # {}
  /\ \E r \in Ingredients :
        /\ smokers[r].smoking = TRUE
        /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
        /\ dealer'   = {}

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* An invariant checking that at most one smoker smokes at any particular  *)
(* moment                                                                  *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1
=============================================================================