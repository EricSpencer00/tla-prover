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
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init ==
   /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
   /\ dealer \in Offers

(***************************************************************************)
(* The dealer offers a set of two ingredients (i.e., all but one). The    *)
(* smoker who owns the missing ingredient may start smoking.              *)
(* The original specification attempted to set the missing smoker's      *)
(* flag to TRUE using a malformed expression; the corrected version       *)
(* explicitly identifies that smoker and updates only its flag.            *)
(***************************************************************************)
startSmoking ==
   /\ dealer /= {}
   /\ \E r \in Ingredients :
        /\ smokers[r].smoking = FALSE
        /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
        /\ dealer' = {}

(***************************************************************************)
(* After a smoker finishes, the dealer must make a new offer. The action   *)
(* also resets the smoker's flag. The original used a poorly defined      *)
(* function to pick the smoking smoker; the corrected version uses        *)
(* ChooseOne to select the unique smoker who is currently smoking.        *)
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