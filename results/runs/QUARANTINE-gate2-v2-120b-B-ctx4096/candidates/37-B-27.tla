---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers
VARIABLE smokers, dealer

(* ------------------------------------------------------------------------ *)
(* Assumptions about the ingredients and the dealer's possible offers.     *)
(* ------------------------------------------------------------------------ *)
ASSUME /\ Offers \subseteq SUBSET Ingredients
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

(* ------------------------------------------------------------------------ *)
(* Type invariant describing the shapes of the state variables.            *)
(* ------------------------------------------------------------------------ *)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

(* ------------------------------------------------------------------------ *)
(* Helper to pick the unique smoker that is currently smoking.             *)
(* ------------------------------------------------------------------------ *)
ChooseOne(S, P(_)) == 
    CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(* ------------------------------------------------------------------------ *)
(* Initial state: no smoker is smoking, dealer holds an arbitrary offer.    *)
(* ------------------------------------------------------------------------ *)
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(* ------------------------------------------------------------------------ *)
(* startSmoking: the dealer has placed an offer; the unique smoker who has *)
(* the missing ingredient begins to smoke, and the dealer clears its       *)
(* offer.  The action is defined with a deterministic choice of that       *)
(* smoker, guaranteeing that every variable is assigned.                   *)
(* ------------------------------------------------------------------------ *)
startSmoking == 
    /\ dealer /= {}
    /\ \E r \in Ingredients :
          /\ dealer = Ingredients \ {r}
          /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
          /\ dealer' = {}

(* ------------------------------------------------------------------------ *)
(* stopSmoking: after a smoker finishes, the dealer picks a new offer.      *)
(* ------------------------------------------------------------------------ *)
stopSmoking == 
    /\ dealer = {}
    /\ LET r == ChooseOne(Ingredients,
                         LAMBDA x : smokers[x].smoking)
       IN /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
          /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(* ------------------------------------------------------------------------ *)
(* Invariant: at most one smoker can be smoking at any moment.             *)
(* ------------------------------------------------------------------------ *)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

====