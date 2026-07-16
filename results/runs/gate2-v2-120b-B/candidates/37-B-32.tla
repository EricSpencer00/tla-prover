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
ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

(***************************************************************************)
(* 'smokers' is a function from the ingredient the smoker has              *)
(* infinite supply of, to a BOOLEAN flag signifying smoker's state         *)
(* (smoking/not smoking)                                                   *)
(* 'dealer' is an element of 'Offers', or the empty set                     *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

(* CHOOSE a unique element from a non‑empty set satisfying a predicate *)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(* When the dealer holds an offer, the smoker whose missing ingredient is
   the one not present in the offer starts smoking.  This action updates
   exactly the smoking flag of that smoker and then clears the dealer. *)
startSmoking ==
    /\ dealer /= {}
    /\ \E r \in Ingredients :
          /\ dealer = Ingredients \ {r}
          /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
          /\ dealer' = {}

(* When no offer is present, one currently‑smoking smoker stops, and the
   dealer picks a new offer.  This action updates exactly the smoking flag
   of the chosen smoker and assigns a fresh offer to the dealer. *)
stopSmoking ==
    /\ dealer = {}
    /\ \E r \in Ingredients :
          /\ smokers[r].smoking = TRUE
          /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
          /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* An invariant checking that at most one smoker smokes at any particular  *)
(* moment                                                                  *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

=============================================================================