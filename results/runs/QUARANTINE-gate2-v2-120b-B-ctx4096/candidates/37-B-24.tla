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
(* 'dealer' is an element of 'Offers', or the empty set                     *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

(* ChooseOne returns the unique element of the set that satisfies P. *)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(***************************************************************************)
(* The initial state: all smokers are idle and the dealer holds a random   *)
(* offer (i.e., a set missing exactly one ingredient).                     *)
(***************************************************************************)
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(***************************************************************************)
(* A smoker may start smoking when the dealer holds an offer.  The smoker *
(* that possesses the missing ingredient (the one not present in the     *)
(* offer) sets his smoking flag to TRUE, and the dealer becomes empty.    *)
(***************************************************************************)
startSmoking == 
    /\ dealer /= {}
    /\ LET missing == Ingredients \ dealer IN
       /\ missing \in Ingredients
       /\ smokers' = [smokers EXCEPT ![missing].smoking = TRUE]
       /\ dealer' = {}

(***************************************************************************)
(* A smoker who is currently smoking may stop.  After he stops, the dealer *
(* receives a new (possibly different) offer.                              *)
(***************************************************************************)
stopSmoking == 
    /\ dealer = {}
    /\ \E r \in Ingredients : smokers[r].smoking = TRUE
    /\ LET r == ChooseOne(Ingredients,
                           LAMBDA x : smokers[x].smoking) IN
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