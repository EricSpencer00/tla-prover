---- MODULE CigaretteSmokers ----
(***************************************************************************)
(* A specification of the cigarette smokers problem, originally            *)
(* described in 1971 by Suhas Patil.                                       *)
(* https://en.wikipedia.org/wiki/Cigarette_smokers_problem                 *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers

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
          /\ dealer \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(***************************************************************************)
(* A smoker starts smoking when the dealer has offered a set of            *)
(* ingredients missing exactly the ingredient that smoker has a supply of   *)
(* (such a set must be non-empty); the dealer's offer is consumed in the     *)
(* same step                                                             *)
(***************************************************************************)
StartSmoking == /\ dealer /= {}
                 /\ smokers' = [r \in Ingredients |-> [smoking |-> {r} \cup 
                                                      dealer = Ingredients]]
                 /\ dealer' = {}

(***************************************************************************)
(* A smoker stops smoking and the dealer re-offers an arbitrary              *)
(* non-empty set missing exactly one ingredient                           *)
(***************************************************************************)
StopSmoking == /\ \E offered \in Offers :
                  /\ smokers' = [smokers EXCEPT ![r \in Ingredients].
                                   IF smokers[r].smoking THEN [smoking |-> FALSE]
                                   ELSE @]
                  /\ dealer' = offered

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(StartSmoking)

(***************************************************************************)
(* An invariant checking that at most one smoker smokes at any particular  *)
(* moment                                                                  *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1
====