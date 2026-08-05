---- MODULE CigaretteSmokers
(***************************************************************************)
(* A specification of the cigarette smokers problem, originally            *)
(* described in 1971 by Suhas Patil.                                       *)
(* https://en.wikipedia.org/wiki/Cigarette_smokers_problem                 *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers

ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

\* When a smoker starts, they take the one missing ingredient and the
\* whole set of available offers (the full table) -- the full set of
\* ingredients.  This is what happens when they are handed the missing
\* ingredient and the full table of the others, and it is also what fixes
\* the TLC error: every variable is now assigned on this transition.
StartSmoking == /\ dealer /= {}
                 /\ smokers' = [r \in Ingredients |->
                                   [smoking |-> {r} \cup dealer = Ingredients]]
                 /\ dealer'  = {}

StopSmoking == /\ dealer = {}
               /\ LET r == ChooseOne(Ingredients,
                                     LAMBDA x : smokers[x].smoking)
                  IN smokers' = [smokers EXCEPT ![r].smoking = FALSE]
               /\ dealer' \in Offers

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* An invariant checking that at most one smoker smokes at any particular  *)
(* moment                                                                  *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1
================================================================================