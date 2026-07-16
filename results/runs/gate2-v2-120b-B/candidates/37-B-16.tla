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
(* 'dealer' is an element of 'Offers', or the empty set                     *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(* Initial state: no one is smoking and the dealer selects any offer *)
Init ==
    /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
    /\ dealer \in Offers

(* The dealer places an offer; the smoker who holds the missing ingredient
   starts smoking.  The 'dealer' variable becomes the empty set to indicate
   that the offer has been taken. *)
startSmoking ==
    /\ dealer # {}
    /\ \E r \in Ingredients :
         /\ dealer = Ingredients \ {r}
         /\ smokers' = [s \in Ingredients |-> 
                          IF s = r THEN [smoking |-> TRUE]
                          ELSE smokers[s]]
         /\ dealer' = {}

(* After a smoker finishes, the dealer puts a new offer on the table. *)
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