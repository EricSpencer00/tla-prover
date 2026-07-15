---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers

VARIABLE smokers, dealer

***************************************************************************
(* 'Ingredients' is a set of ingredients, originally                       *)
(* {matches, paper, tobacco}. 'Offers' is a subset of subsets of           *)
(* ingredients, each missing just one ingredient                           *)
***************************************************************************
ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

***************************************************************************
(* 'smokers' is a function from the ingredient the smoker has              *)
(* infinite supply of, to a BOOLEAN flag signifying smoker's state         *)
(* (smoking/not smoking)                                                   *)
(* 'dealer' is an element of 'Offers', or an empty set                     *)
***************************************************************************
TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(* The smoker who owns the missing ingredient begins smoking.               *)
(* All other smokers stay non‑smoking. The dealer becomes empty (no offer). *)
startSmoking == 
    /\ dealer # {}
    /\ \E missing \in Ingredients :
          /\ dealer = Ingredients \ {missing}
          /\ smokers' = [r \in Ingredients |-> 
                           [smoking |-> IF r = missing THEN TRUE ELSE FALSE]]
          /\ dealer' = {}

(* After a smoker finishes, the dealer must choose a new offer before any   *)
(* further smoking can occur.                                               *)
stopSmoking == 
    /\ dealer = {}
    /\ \E r \in Ingredients :
          /\ smokers[r].smoking = TRUE
          /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
          /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(* At most one smoker may be smoking at any moment. *)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

====