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
          /\ dealer \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(*
  The deal with [smoking |-> {r} \cup dealer = Ingredients] was a typo: it
  made the whole expression a set instead of a BOOLEAN record, so TLC
  flagged that the dealer was left unassigned when startSmoking fired.
  The intent is to set the chosen smoker's smoking flag to TRUE exactly when
  the ingredients on the table plus that smoker's own infinite supply cover
  the whole set.
*)
startSmoking == /\ dealer /= {}
                /\ smokers' = [r \in Ingredients |->
                                 IF {r} \cup dealer = Ingredients
                                 THEN [smoking |-> TRUE]
                                 ELSE [smoking |-> FALSE]]
                /\ dealer' = {}

stopSmoking == /\ dealer = {}
               /\ LET r == ChooseOne(Ingredients,
                                     LAMBDA x : smokers[x].smoking)
                  IN smokers' = [smokers EXCEPT ![r].smoking = FALSE]
               /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* An invariant checking that at most one smoker smokes at any particular  *)
(* moment                                                                  *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1
====