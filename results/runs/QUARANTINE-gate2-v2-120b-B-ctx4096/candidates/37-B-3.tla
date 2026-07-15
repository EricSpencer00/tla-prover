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
(* 'dealer' is an element of 'Offers', or an empty set                     *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

(***************************************************************************)
(* ChooseOne returns the unique element of a set that satisfies a predicate *)
(***************************************************************************)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(***************************************************************************)
(* When the dealer offers a set of two ingredients, the smoker whose      *)
(* missing ingredient is exactly the one not present in the offer can      *)
(* start smoking. We model this by setting his `smoking` flag to TRUE and  *)
(* clearing the dealer (the offer has been taken).                         *)
(***************************************************************************)
startSmoking == /\ dealer /= {}
                 /\ \E r \in Ingredients :
                       /\ r \notin dealer                \* r is the missing ingredient
                       /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
                 /\ dealer' = {}

(***************************************************************************)
(* After a smoker finishes, the dealer selects a new offer. The smoker that*)
(* was smoking is set back to FALSE.                                        *)
(***************************************************************************)
stopSmoking == /\ dealer = {}
               /\ LET r == ChooseOne(Ingredients,
                                      LAMBDA x : smokers[x].smoking)
                  IN /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
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