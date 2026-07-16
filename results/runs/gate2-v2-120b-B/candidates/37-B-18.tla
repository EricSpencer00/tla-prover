---- MODULE CigaretteSmokers ----
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
ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

(***************************************************************************)
(* 'smokers' is a function from the ingredient the smoker has              *)
(* infinite supply of, to a BOOLEAN flag signifying smoker's state         *)
(* (smoking/not smoking)                                                   *)
(* 'dealer' is an element of 'Offers', or an empty set                     *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

ChooseOne(S, P(_)) ==
  CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(* Initial state: no one is smoking and the dealer holds some offer. *)
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(* startSmoking: the dealer provides an offer and exactly one smoker,
   the one missing the offered ingredient, starts smoking. *)
startSmoking ==
  /\ dealer /= {}
  /\ \E r \in Ingredients :
        /\ smokers[r].smoking = FALSE
        /\ r \notin dealer               \* r is the ingredient the smoker has
        /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
        /\ dealer' = {}

(* stopSmoking: the currently smoking smoker finishes and the dealer
   picks a new offer. *)
stopSmoking ==
  /\ dealer = {}
  /\ \E r \in Ingredients :
        /\ smokers[r].smoking = TRUE
        /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
        /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* An invariant checking that at most one smoker smokes at any particular  *)
(* moment                                                                  *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

=============================================================================