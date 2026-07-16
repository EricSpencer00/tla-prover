---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers
VARIABLE smokers, dealer

(***************************************************************************)
(* Types and auxiliary definitions                                         *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(***************************************************************************)
(* Initial predicate                                                       *)
(***************************************************************************)
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

(* The smoker whose missing ingredient is offered starts smoking.        *)
startSmoking == /\ dealer /= {}
                /\ \E missing \in Ingredients :
                       /\ dealer = Ingredients \ {missing}
                       /\ smokers' = [r \in Ingredients |-> 
                                        IF r = missing
                                           THEN [smoking |-> TRUE]
                                           ELSE smokers[r]]
                /\ dealer' = {}

(* An active smoker finishes smoking and the dealer chooses a new offer. *)
stopSmoking == /\ \E r \in Ingredients : smokers[r].smoking
               /\ smokers' = [s \in smokers EXCEPT ![r].smoking = FALSE]
               /\ dealer' \in Offers

(***************************************************************************)
(* Next-state relation                                                     *)
(***************************************************************************)
Next == startSmoking \/ stopSmoking

(***************************************************************************)
(* Full specification                                                      *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Optional weak fairness (not required for the safety invariant)         *)
(***************************************************************************)
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* Safety invariant: at most one smoker smokes at any time                *)
(***************************************************************************)
AtMostOne == Cardinality({ r \in Ingredients : smokers[r].smoking }) <= 1

=============================================================================