-------------------------- MODULE CigaretteSmokers --------------------------
(***************************************************************************)
(* A specification of the cigarette smokers problem, originally            *)
(* described in 1971 by Suhas Patil.                                       *)
(* https://en.wikipedia.org/wiki/Cigarette_smokers_problem                 *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers
VARIABLE smokers, dealer

(***************************************************************************)
(* 'Ingredients' is a set of ingredients, originally                       *)
(* {matches, paper, tobacco}. 'Offers' is a subset of subsets of           *)
(* ingredients, each missing just one ingredient                           *)
(***************************************************************************)
ASSUME /\
    Offers \subseteq SUBSET Ingredients
    /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

(***************************************************************************)
(* 'smokers' is a function from the ingredient the smoker has              *)
(* infinite supply of, to a BOOLEAN flag signifying smoker's state         *)
(* (smoking/not smoking)                                                   *)
(* 'dealer' is an element of 'Offers', or an empty set                     *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

(***************************************************************************)
(* ChooseOne selects the unique element satisfying the predicate;           *)
(* it is used only when such an element is guaranteed to exist.            *)
(***************************************************************************)
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(***************************************************************************)
(* Initial state: no smoker is smoking, and the dealer holds an arbitrary *)
(* offer (i.e., any subset missing exactly one ingredient).                *)
(***************************************************************************)
Init ==
    /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
    /\ dealer \in Offers

(***************************************************************************)
(* startSmoking: an offer is placed on the table (dealer) and the smoker  *)
(* who owns the missing ingredient starts smoking.                          *)
(* The update to `smokers` sets the appropriate smoker's `smoking` flag to *)
(* TRUE; all other smokers remain unchanged. The dealer is unchanged.      *)
(***************************************************************************)
startSmoking ==
    /\ dealer /= {}
    /\ LET missing == Ingredients \ dealer IN
       /\ missing \in Ingredients
       /\ smokers' = [smokers EXCEPT ![missing].smoking = TRUE]
       /\ dealer' = dealer

(***************************************************************************)
(* stopSmoking: the currently smoking smoker finishes smoking and the      *)
(* dealer picks a new offer. The transition clears the smoker's flag and   *)
(* assigns a fresh offer (any element of Offers).                          *)
(***************************************************************************)
stopSmoking ==
    /\ dealer \in Offers
    /\ LET r == ChooseOne(
                    Ingredients,
                    LAMBDA x : smokers[x].smoking
                )
       IN
          /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
          /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* An invariant checking that at most one smoker smokes at any particular  *)
(* moment                                                                  *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

=============================================================================