---- MODULE CigaretteSmokers ----
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
(* 'dealer' is either an element of 'Offers' or the empty set               *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

(***************************************************************************)
(* ChooseOne returns the unique element of a set that satisfies the predicate*)
(***************************************************************************)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(***************************************************************************)
(* An action where the dealer places an offer on the table and the smoker  *)
(* that has the missing ingredient starts smoking. The dealer then becomes *)
(* empty (represented by the empty set).                                    *)
(***************************************************************************)
startSmoking == 
    /\ dealer /= {}
    /\ \E r \in Ingredients :
          /\ \A i \in Ingredients : 
                (i \in dealer) => smokers[i].smoking = FALSE
          /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
          /\ dealer' = {}

(***************************************************************************)
(* An action where the currently smoking smoker stops, the dealer puts a   *)
(* new offer on the table, and all smokers become non‑smoking.              *)
(***************************************************************************)
stopSmoking == 
    /\ dealer = {}
    /\ \E r \in Ingredients :
          /\ smokers[r].smoking = TRUE
          /\ smokers' = [r \in Ingredients |-> [smoking |-> FALSE]]
          /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* Invariant that at most one smoker smokes at any moment                    *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

====