---- MODULE CigaretteSmokers ----
(***************************************************************************)
(* A specification of the cigarette smokers problem, originally            *)
(* described in 1971 by Suhas Patil.                                       *)
(* https://en.wikipedia.org/wiki/Cigarette_smokers_problem                 *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers

ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

VARIABLES smokers, dealer

TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer  \in Offers

(***************************************************************************)
(* A smoker may start, provided the dealer has put an offer down: the       *)
(* smoker takes the dealer's offer and starts smoking                          *)
(***************************************************************************)
StartSmoking ==
    /\ dealer # {}
    /\ \E r \in Ingredients :
        /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
        /\ dealer' = {}
    /\ UNCHANGED dealers

(***************************************************************************)
(* A smoker may stop, providing the dealer has no offer outstanding: the     *)
(* chosen smoker stops and the dealer proceeds to make its next offer        *)
(***************************************************************************)
StopSmoking ==
    /\ dealer = {}
    /\ \E r \in {x \in Ingredients : smokers[x].smoking} :
        /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
        /\ dealer' \in Offers

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* An invariant checking that at most one smoker smokes at any particular  *)
(* moment                                                                  *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

=============================================================================