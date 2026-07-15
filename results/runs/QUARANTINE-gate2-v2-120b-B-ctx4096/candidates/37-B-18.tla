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
(* A smoker can start smoking only when the dealer offers a set of        *)
(* two ingredients (i.e., a set missing exactly one ingredient). The      *)
(* missing ingredient identifies the smoker that may smoke.                *)
(* The action sets that smoker's 'smoking' flag to TRUE and clears the    *)
(* dealer.                                                                  *)
(***************************************************************************)
startSmoking == 
    /\ dealer /= {}
    /\ \E r \in Ingredients :
          /\ r \notin dealer               \* r is the missing ingredient
          /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
          /\ dealer' = {}

(***************************************************************************)
(* When a smoker finishes, the system must choose the unique smoker that   *)
(* is currently smoking, set its flag to FALSE, and make the dealer offer   *)
(* a new (any) set from Offers.                                             *)
(***************************************************************************)
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