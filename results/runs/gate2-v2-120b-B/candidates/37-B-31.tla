---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers

VARIABLE smokers, dealer

(***************************************************************************)
(* Type correctness predicate                                               *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

(***************************************************************************)
(* Helper to choose the unique element from a set satisfying a predicate  *)
(***************************************************************************)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(***************************************************************************)
(* Initial state: no smoker is smoking, dealer holds some offer            *)
(***************************************************************************)
Init ==
    /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
    /\ dealer \in Offers

(***************************************************************************)
(* startSmoking: dealer gives its two ingredients to the smoker that     *)
(* lacks the third one; that smoker starts smoking; the dealer becomes    *)
(* empty (represented by the empty set)                                   *)
(***************************************************************************)
startSmoking ==
    /\ dealer /= {}
    /\ \E missing \in Ingredients :
         /\ dealer = Ingredients \ {missing}
         /\ smokers' = [smokers EXCEPT ![missing].smoking = TRUE]
    /\ dealer' = {}

(***************************************************************************)
(* stopSmoking: the smoker that is currently smoking finishes, and the    *)
(* dealer picks a new offer.                                               *)
(***************************************************************************)
stopSmoking ==
    /\ dealer = {}
    /\ \E r \in Ingredients :
         /\ smokers[r].smoking = TRUE
         /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
    /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariant: at most one smoker is smoking at any moment                *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

====