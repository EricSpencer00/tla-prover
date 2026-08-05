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
(* (smoking/not smoking). 'dealer' is an element of 'Offers', or an empty    *)
(* set                                                                     *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer \in Offers \cup {null}

vars == <<smokers, dealer>>

\* A single smoker takes the missing ingredient and smokes: the dealer hands
\* over the offer piece by piece, and nothing is left out.
startSmoking ==
  /\ dealer # null
  /\ \E r \in Ingredients :
       smokers' = [smokers EXCEPT ![r] = [smoking |-> {r} \cup dealer]]
  /\ dealer' = null

\* When the offer is exhausted, the smoker stops and the dealer re-loads.
stopSmoking ==
  /\ dealer = null
  /\ \E r \in Ingredients :
       /\ smokers[r].smoking
       /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
       /\ dealer' = CHOOSE x \in Offers : TRUE

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(startSmoking) /\ WF_vars(stopSmoking)

(***************************************************************************)
(* At most one smoker smokes at any particular moment                     *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1
====