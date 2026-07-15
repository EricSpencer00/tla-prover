---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers
VARIABLE smokers, dealer

(* ==================================================================================
   Type definitions
   ================================================================================== *)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

(* ==================================================================================
   Helper definition: Choose exactly one element of a set satisfying a predicate
   ================================================================================== *)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(* ==================================================================================
   Initial predicate
   ================================================================================== *)
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(* ==================================================================================
   Action: a smoker starts smoking
   The smoker whose ingredient is missing from the dealer's offer becomes the
   active smoker. All other smokers remain non‑smoking. The dealer becomes empty.
   ================================================================================== *)
startSmoking == 
    /\ dealer /= {}
    /\ \E r \in Ingredients :
          /\ dealer = Ingredients \ {r}
          /\ dealer' = {}
          /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]

(* ==================================================================================
   Action: the active smoker stops smoking
   A smoker that is currently smoking is chosen (there is at most one by the
   invariant). That smoker stops, and the dealer picks a new offer.
   ================================================================================== *)
stopSmoking == 
    /\ dealer = {}
    /\ \E r \in Ingredients :
          /\ smokers[r].smoking = TRUE
          /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
          /\ dealer' \in Offers

(* ==================================================================================
   Next-state relation
   ================================================================================== *)
Next == startSmoking \/ stopSmoking

(* ==================================================================================
   Variables tuple for stuttering steps
   ================================================================================== *)
vars == <<smokers, dealer>>

(* ==================================================================================
   Full specification
   ================================================================================== *)
Spec == Init /\ [][Next]_vars

(* ==================================================================================
   Invariant: at most one smoker may be smoking at any time
   ================================================================================== *)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

=============================================================================