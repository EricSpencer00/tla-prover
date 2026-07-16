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
(* infinite supply of, to a record containing a BOOLEAN flag signifying    *)
(* the smoker's state (smoking / not smoking).                             *)
(* 'dealer' is either an element of 'Offers' or the empty set (no offer).  *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

(* Helper to choose the unique smoker whose record says they are smoking. *)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init ==
  /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
  /\ dealer \in Offers

(* When the dealer holds an offer, exactly the smoker who possesses the
   missing ingredient begins to smoke.  The dealer then becomes empty. *)
startSmoking ==
  /\ dealer /= {}
  /\ \E missing \in Ingredients :
        /\ missing \notin dealer
        /\ /\ smokers' = [r \in Ingredients |-> 
                            [smoking |-> IF r = missing THEN TRUE ELSE FALSE]]
           /\ dealer' = {}

(* When no offer is present, the currently smoking smoker stops, and the
   dealer selects a new offer. *)
stopSmoking ==
  /\ dealer = {}
  /\ LET r == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking)
     IN /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
        /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* An invariant checking that at most one smoker smokes at any particular  *)
(* moment.                                                                 *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

=============================================================================