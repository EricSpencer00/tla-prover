---- MODULE CigaretteSmokers --------------------------
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
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer  = {}

(* --------------------------------------------------------------------- *)
(* Action: startSmoking                                                 *)
(* The dealer puts three ingredients on the table (the set `dealer`)   *)
(* and exactly one smoker whose missing ingredient is the one not       *)
(* present in `dealer` begins smoking (its `smoking` flag becomes TRUE). *)
(* --------------------------------------------------------------------- *)
startSmoking == 
    /\ dealer = {}                                   \* dealer currently empty
    /\ \E d \in Offers : 
          /\ dealer' = d                              \* dealer now offers a set of three
          /\ \E r \in Ingredients : 
                /\ r \notin d                         \* r is the missing ingredient
                /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
                /\ \A s \in Ingredients : s # r => 
                       smokers'[s].smoking = FALSE   \* other smokers stay non‑smoking
    /\ UNCHANGED smokers \* (handled by the EXCEPT construct above)

(* --------------------------------------------------------------------- *)
(* Action: stopSmoking                                                  *)
(* The smoker that is currently smoking finishes, resetting its flag,   *)
(* and the dealer clears the table (returns to the empty set).          *)
(* --------------------------------------------------------------------- *)
stopSmoking == 
    /\ dealer # {}                                   \* there is an offer on the table
    /\ \E r \in Ingredients : 
          /\ smokers[r].smoking                       \* r is the smoking smoker
          /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
    /\ dealer' = {}                                   \* table cleared
    /\ UNCHANGED smokers \* (already updated by EXCEPT)

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* An invariant checking that at most one smoker smokes at any particular  *)
(* moment                                                                  *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

====