---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers

VARIABLE smokers, dealer

(***************************************************************************)
(* Assumptions about the set of possible offers                           *)
(***************************************************************************)
ASSUME /\ Offers \subseteq SUBSET Ingredients
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

(***************************************************************************)
(* Helper to pick the unique smoker whose flag is TRUE                     *)
(***************************************************************************)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(***************************************************************************)
(* Initial state                                                          *)
(***************************************************************************)
Init ==
  /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
  /\ dealer   \in Offers

(***************************************************************************)
(* Action: a smoker starts smoking                                       *)
(***************************************************************************)
startSmoking ==
  /\ dealer /= {}
  /\ \E r \in Ingredients :
        /\ r \notin dealer               \* the smoker who owns the missing ingredient
        /\ dealer' = {}
        /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
  \/ /\ dealer' = dealer
        /\ smokers' = smokers            \* stutter when no smoker can start

(***************************************************************************)
(* Action: a smoker finishes smoking                                      *)
(***************************************************************************)
stopSmoking ==
  /\ dealer = {}
  /\ \E r \in Ingredients :
        /\ smokers[r].smoking = TRUE
        /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
        /\ dealer' \in Offers
  \/ /\ dealer' = dealer
        /\ smokers' = smokers            \* stutter when no smoker is smoking

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* Invariant: at most one smoker is smoking at any time                  *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

====