---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers

VARIABLE smokers, dealer

(* --type invariants --------------------------------------------------- *)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}

(* --initial state ------------------------------------------------------ *)
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(* --actions ------------------------------------------------------------ *)

(* startSmoking: the dealer provides the missing ingredient and a
   smoker begins smoking.  The dealer becomes empty after this. *)
startSmoking ==
    /\ dealer /= {}
    /\ \E r \in Ingredients :
          /\ r \notin dealer
          /\ /\ smokers' = [smokers EXCEPT ![r].smoking = TRUE]
             /\ dealer' = {}

(* stopSmoking: the current smoker finishes and the dealer picks a new
   offer. *)
stopSmoking ==
    /\ dealer = {}
    /\ \E r \in Ingredients :
          /\ smokers[r].smoking
          /\ /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
             /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

(* --behavior specification -------------------------------------------- *)
Spec == Init /\ [][Next]_<<smokers, dealer>>
FairSpec == Spec /\ WF_<<smokers, dealer>>(Next)

(* --invariant ---------------------------------------------------------- *)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

====