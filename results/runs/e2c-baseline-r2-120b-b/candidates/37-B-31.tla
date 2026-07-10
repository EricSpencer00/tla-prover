---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers
VARIABLE smokers, dealer

(*-------------------------------------------------------------------*)
(*  Ingredients is the set of three items (e.g., matches, paper,     *)
(*  tobacco).  Offers is the set of subsets of Ingredients that are *)
(*  missing exactly one ingredient.                                   *)
(*-------------------------------------------------------------------*)
ASSUME /\ Offers \subseteq SUBSET Ingredients
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

(*-------------------------------------------------------------------*)
(*  State variables                                                   *)
(*-------------------------------------------------------------------*)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

(*-------------------------------------------------------------------*)
(*  Helper: choose the unique element satisfying a predicate          *)
(*-------------------------------------------------------------------*)
ChooseOne(S, P(_)) ==
  CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x

(*-------------------------------------------------------------------*)
(*  Initial state                                                    *)
(*-------------------------------------------------------------------*)
Init ==
  /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
  /\ dealer \in Offers

(*-------------------------------------------------------------------*)
(*  When the dealer has placed an offer, the unique smoker whose     *)
(*  ingredient is missing starts smoking and the dealer becomes      *)
(*  empty (represented by the empty set).                             *)
(*-------------------------------------------------------------------*)
startSmoking ==
  /\ dealer /= {}
  /\ LET r == ChooseOne(Ingredients \ dealer, LAMBDA x : TRUE) IN
       /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
       /\ dealer'   = {}

(*-------------------------------------------------------------------*)
(*  When no offer is on the table, the smoker that is currently      *)
(*  smoking stops, and the dealer puts a new offer on the table.     *)
(*-------------------------------------------------------------------*)
stopSmoking ==
  /\ dealer = {}
  /\ LET r == ChooseOne(Ingredients,
                        LAMBDA x : smokers[x].smoking) IN
       /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
       /\ dealer'   \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(*-------------------------------------------------------------------*)
(*  Invariant: at most one smoker may be smoking at any moment       *)
(*-------------------------------------------------------------------*)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1
====