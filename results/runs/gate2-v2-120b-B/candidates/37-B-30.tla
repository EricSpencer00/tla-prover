---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers

VARIABLE smokers, dealer

(* Type correctness *)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

(* Helper to pick a unique element satisfying a predicate *)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(* Initial state *)
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(* Define the set of ingredients that the smoker currently holds.
   For a smoker whose own ingredient is r, the set is the union of
   r and the ingredient(s) offered by the dealer. *)
smokerSet(r) == {r} \cup dealer

(* startSmoking: the dealer provides an offer; the unique smoker whose
   own ingredient is missing from that offer begins smoking. *)
startSmoking ==
   /\ dealer /= {}
   /\ \E r \in Ingredients :
        /\ /\ r \notin dealer               \* r is the missing ingredient
          /\ smokers[r].smoking = FALSE    \* that smoker is currently idle
          /\ /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
             /\ dealer' = {}                \* the dealer clears its offer

(* stopSmoking: the current smoker finishes, and the dealer picks a new offer. *)
stopSmoking ==
   /\ dealer = {}
   /\ \E r \in Ingredients :
        /\ /\ smokers[r].smoking = TRUE
          /\ LET newDealer == CHOOSE o \in Offers : o # {}
             IN /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
                /\ dealer' = newDealer

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_<<smokers, dealer>>

FairSpec == Spec /\ WF_<<smokers, dealer>>(Next)

(* Invariant: at most one smoker may be smoking at any time *)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

====