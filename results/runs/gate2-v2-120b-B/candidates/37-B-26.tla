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
(* 'Ingredients' is a set of ingredients, originally                       *)
(* {matches, paper, tobacco}. 'Offers' is a subset of subsets of           *)
(* ingredients, each missing just one ingredient                           *)
(***************************************************************************)
ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

(***************************************************************************)
(* 'smokers' is a function from the ingredient the smoker has              *)
(* infinite supply of, to a BOOLEAN flag signifying smoker's state         *)
(* (smoking/not smoking)                                                   *)
(* 'dealer' is an element of 'Offers', or an empty set                     *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(***************************************************************************)
(* The specification assumes that initially the dealer chooses a          *)
(* *complete* offer (i.e., a set containing *all* ingredients).  This      *)
(* matches the original intent of the problem where the dealer places     *)
(* the three ingredients on the table, after which one smoker picks the  *)
(* missing one.                                                             *)
(***************************************************************************)
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(***************************************************************************)
(* startSmoking: The dealer supplies the three ingredients (the full set) *)
(*               and the smoker who possesses the missing ingredient      *)
(*               begins smoking.  The action must assign **both**         *)
(*               variables to avoid the TLC error.                         *)
(***************************************************************************)
startSmoking ==
    /\ dealer = {}
    /\ LET missing == CHOOSE i \in Ingredients : i \notin dealer
           newDeal  == Ingredients \ {missing}
       IN /\ dealer' = newDeal
          /\ smokers' = [smokers EXCEPT ![missing].smoking = TRUE]

(***************************************************************************)
(* stopSmoking: The smoker who is currently smoking stops, and the       *)
(*              dealer clears the table (dealer becomes the empty set).   *)
(*              The action also assigns both variables.                    *)
(***************************************************************************)
stopSmoking ==
    /\ \E r \in Ingredients : smokers[r].smoking = TRUE
    /\ LET r == ChooseOne({i \in Ingredients : smokers[i].smoking},
                         LAMBDA x : TRUE)
       IN /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
          /\ dealer' = {}

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* An invariant checking that at most one smoker smokes at any particular  *)
(* moment                                                                  *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

====