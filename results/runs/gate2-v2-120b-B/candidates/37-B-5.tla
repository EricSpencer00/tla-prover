---- MODULE CigaretteSmokers ----
(* A specification of the cigarette smokers problem, originally
   described in 1971 by Suhas Patil.
   https://en.wikipedia.org/wiki/Cigarette_smokers_problem
*)

EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokers, dealer

(*-------------------------------------------------------------------*)
(* Assumptions about the constant sets                               *)
(*-------------------------------------------------------------------)
ASSUME /\ Offers \subseteq SUBSET Ingredients
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

(*-------------------------------------------------------------------*)
(* Type invariant                                                    *)
(*-------------------------------------------------------------------)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

(*-------------------------------------------------------------------*)
(* Helper: choose the unique element that satisfies a predicate       *)
(*-------------------------------------------------------------------)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(*-------------------------------------------------------------------*)
(* Initial state                                                     *)
(*-------------------------------------------------------------------)
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(*-------------------------------------------------------------------*)
(* Action: a smoker starts smoking                                   *)
(*-------------------------------------------------------------------)
startSmoking ==
    /\ dealer /= {}
    /\ \E r \in Ingredients :
         /\ smokers[r].smoking = FALSE
         /\ dealersFull = {r} \cup dealer
         /\ dealersFull = Ingredients
         /\ /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
            /\ dealer'  = {}
    /\ UNCHANGED <<>>

(*-------------------------------------------------------------------*)
(* Action: a smoker stops smoking                                    *)
(*-------------------------------------------------------------------)
stopSmoking ==
    /\ dealer = {}
    /\ \E r \in Ingredients :
         /\ smokers[r].smoking = TRUE
         /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
         /\ dealer' \in Offers
    /\ UNCHANGED <<>>

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(*-------------------------------------------------------------------*)
(* Invariant: at most one smoker smokes at any moment                *)
(*-------------------------------------------------------------------)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

====