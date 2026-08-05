---- MODULE CigaretteSmokers
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers

ASSUME /\ Offers \subseteq SUBSET Ingredients
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

\* The dealer may hand out a single matching set of ingredients (a set
\* missing exactly one ingredient) when it is not already handing one
\* out. The smoker who owns the missing ingredient starts smoking once
\* the dealer's set is empty.
startSmoking == /\ dealer /= {}
                /\ smokers' = [r \in Ingredients |-> [smoking |-> {r} \cup
                                                      dealer = Ingredients]]
                /\ dealer' = {}

\* When no matching set is in circulation, the smoking smoker finishes
\* and the dealer is free to hand out a fresh set.
stopSmoking == /\ dealer = {}
               /\ LET r == ChooseOne(Ingredients,
                                     LAMBDA x : smokers[x].smoking)
                  IN smokers' = [smokers EXCEPT ![r].smoking = FALSE]
               /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* Only one smoker smokes at a time -- the dealer never hands out two      *)
(* complimentary ingredient sets at once, and a smoker only starts smoking  *)
(* when the dealer's set is empty.                                          *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1
====