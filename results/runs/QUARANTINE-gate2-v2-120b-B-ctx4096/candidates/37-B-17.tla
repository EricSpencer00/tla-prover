---- MODULE CigaretteSmokers ----
(***************************************************************************)
(* A specification of the cigarette smokers problem, originally            *)
(* described in 1971 by Suhas Patil.                                       *)
(* https://en.wikipedia.org/wiki/Cigarette_smokers_problem                 *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers

VARIABLE smokers, dealer

(***************************************************************************)
(* Assumptions about the ingredient set and the possible offers.          *)
(***************************************************************************)
ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

(***************************************************************************)
(* Type invariant (kept for readability; not used as a separate invariant).*)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking |-> BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

(***************************************************************************)
(* ChooseOne selects a unique element satisfying a predicate, if one       *)
(* exists.  It is used when a smoker finishes smoking.                     *)
(***************************************************************************)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(***************************************************************************)
(* Initial state: all smokers are not smoking, dealer holds any offer.      *)
(***************************************************************************)
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(***************************************************************************)
(* startSmoking: the dealer presents an offer, exactly one smoker (the    *)
(* one who does NOT have the missing ingredient) begins smoking, and the *)
(* dealer becomes empty.                                                    *)
(***************************************************************************)
startSmoking == /\ dealer /= {}
                /\ \E r \in Ingredients :
                      /\ ~ r \in dealer               \* r is the smoker who has the missing ingredient
                      /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
                      /\ dealer' = {}

(***************************************************************************)
(* stopSmoking: after a smoker finishes, the dealer selects a new offer.  *)
(* Exactly one smoker that was smoking becomes not smoking.                *)
(***************************************************************************)
stopSmoking == /\ dealer = {}
               /\ \E r \in Ingredients :
                     /\ smokers[r].smoking = TRUE
                     /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
                     /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariant: at most one smoker is smoking at any moment.                 *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

=============================================================================