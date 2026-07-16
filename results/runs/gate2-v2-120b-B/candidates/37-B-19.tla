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

ChooseOne(S, P(_)) == 
  CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(***************************************************************************)
(* The dealer places the two missing ingredients on the table, and the    *)
(* smoker who has the third ingredient begins to smoke.                    *)
(* In the original formulation the dealer's set of ingredients becomes    *)
(* empty while the chosen smoker's flag becomes TRUE.                       *)
(***************************************************************************)
startSmoking == 
  /\ dealer # {}
  /\ \E r \in Ingredients :
        /\ smokers[r].smoking = FALSE
        /\ dealersMissing = Ingredients \ {r}
        /\ dealersMissing \subseteq dealer
        /\ dealer' = {}
        /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]

(***************************************************************************)
(* After a smoker finishes, the dealer picks a new offer (any subset of    *)
(* ingredients missing exactly one ingredient) and all smokers are set to *)
(* FALSE again.                                                             *)
(***************************************************************************)
stopSmoking == 
  /\ dealer = {}
  /\ \E r \in Ingredients :
        /\ smokers[r].smoking = TRUE
        /\ dealer' \in Offers
        /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* An invariant checking that at most one smoker smokes at any particular  *)
(* moment                                                                  *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

=============================================================================