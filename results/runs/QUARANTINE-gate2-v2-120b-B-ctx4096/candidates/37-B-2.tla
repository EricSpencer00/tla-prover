---- MODULE CigaretteSmokers ----
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
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

ChooseOne(S, P(_)) == 
    CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(***************************************************************************)
(* When the dealer has placed an offer, the smoker who owns the missing    *)
(* ingredient begins smoking. The dealer then becomes empty.               *)
(***************************************************************************)
startSmoking == 
    /\ dealer /= {}
    /\ LET missing == Ingredients \ dealer IN
       /\ \E r \in missing :
            /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
            /\ dealer' = {}

(***************************************************************************)
(* When the dealer is empty, the currently smoking smoker stops. The dealer *)
(* then chooses a new offer from the set of possible offers.                *)
(***************************************************************************)
stopSmoking == 
    /\ dealer = {}
    /\ \E r \in Ingredients :
         /\ smokers[r].smoking
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

====