---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers
VARIABLE smokers, dealer

(* ------------------------------------------------------------------------ *)
(* Type correctness predicate                                                *)
(* ------------------------------------------------------------------------ *)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

(* ------------------------------------------------------------------------ *)
(* Helper: Choose the unique element satisfying a predicate                  *)
(* ------------------------------------------------------------------------ *)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(* ------------------------------------------------------------------------ *)
(* Initial state                                                            *)
(* ------------------------------------------------------------------------ *)
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(* ------------------------------------------------------------------------ *)
(* Action: start smoking                                                   *)
(* ------------------------------------------------------------------------ *)
(* The dealer offers a set of two ingredients (i.e., everything except the
   ingredient of the smoker who will light). The smoker whose missing ingredient
   is exactly the one absent from the offer begins to smoke. The dealer then
   becomes empty, indicating that the offer has been taken. *)
startSmoking ==
  /\ dealer /= {}
  /\ \E s \in Ingredients :
        /\ dealer = Ingredients \ {s}
        /\ smokers' = [r \in Ingredients |-> 
                         IF r = s THEN [smoking |-> TRUE]
                         ELSE smokers[r]]
        /\ dealer' = {}

(* ------------------------------------------------------------------------ *)
(* Action: stop smoking                                                    *)
(* ------------------------------------------------------------------------ *)
stopSmoking ==
  /\ dealer = {}
  /\ \E s \in Ingredients :
        /\ smokers[s].smoking = TRUE
        /\ smokers' = [r \in Ingredients |-> 
                         IF r = s THEN [smoking |-> FALSE]
                         ELSE smokers[r]]
        /\ dealer' \in Offers

(* ------------------------------------------------------------------------ *)
(* Next-state relation                                                       *)
(* ------------------------------------------------------------------------ *)
Next == startSmoking \/ stopSmoking

(* ------------------------------------------------------------------------ *)
(* Full behavior specification                                               *)
(* ------------------------------------------------------------------------ *)
Spec == Init /\ [][Next]_<<smokers, dealer>>
FairSpec == Spec /\ WF_<<smokers, dealer>>(Next)

(* ------------------------------------------------------------------------ *)
(* Invariant: at most one smoker is smoking at any moment                  *)
(* ------------------------------------------------------------------------ *)
AtMostOne == Cardinality({ r \in Ingredients : smokers[r].smoking }) <= 1

=============================================================================