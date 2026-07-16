---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers

VARIABLE smokers, dealer

(* Type invariant *)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

(* Choose a unique element from a set satisfying a predicate *)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(* Initial state: all smokers are not smoking, dealer holds some offer *)
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(* A smoker that owns the missing ingredient starts smoking,
   and the dealer becomes empty. *)
startSmoking ==
  /\ dealer /= {}
  /\ \E missing \in Ingredients :
        /\ missing \notin dealer
        /\ LET r == missing IN
              /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
              /\ dealer' = {}

(* When the dealer is empty, exactly one smoker who is currently smoking
   stops, and the dealer receives a new offer. *)
stopSmoking ==
  /\ dealer = {}
  /\ \E r \in Ingredients :
        /\ smokers[r].smoking = TRUE
        /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
        /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars

(* Invariant: at most one smoker is smoking at any time *)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

====