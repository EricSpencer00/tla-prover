---- MODULE CigaretteSmokers ----
EXTENDS Naturals, Sequences, TLC

CONSTANT Ingredients
CONSTANT Offers

VARIABLES smokers, offer

(*--- Types and State ---*)
Smokers == [ing \in Ingredients |-> BOOLEAN]

(* Initial state: no one is smoking, a nondeterministic valid offer *)
Init ==
    /\ smokers = [ing \in Ingredients |-> FALSE]
    /\ offer \in Offers

(* Helper: the set of ingredients that are currently being used (offer + smoker's own) *)
UsedIngredients == IF offer = {} THEN {} ELSE offer \cup {ing \in Ingredients: smokers[ing]}

(*--- Actions ---*)

(* A smoker whose own ingredient completes the set starts smoking *)
StartSmoking ==
    /\ offer # {}
    /\ \E ing \in Ingredients :
          /\ smokers[ing] = FALSE
          /\ offer = Ingredients \ {ing}
          /\ smokers' = [smokers EXCEPT ![ing] = TRUE]
          /\ offer' = {}
    /\ UNCHANGED << >>

(* The currently smoking smoker stops and the dealer places a new offer *)
StopSmoking ==
    /\ offer = {}
    /\ \E ing \in Ingredients :
          /\ smokers[ing] = TRUE
          /\ smokers' = [smokers EXCEPT ![ing] = FALSE]
          /\ offer' \in Offers
    /\ UNCHANGED << >>

Next == StartSmoking \/ StopSmoking

(*--- Specification ---*)
Spec == Init /\ [][Next]_<<smokers, offer>>

(*--- Safety Invariant: At most one smoker is smoking ---*)
AtMostOne ==
    Cardinality({ing \in Ingredients : smokers[ing]}) <= 1

(*--- Type correctness invariant (optional, but required by the cfg) ---*)
TypeOK ==
    /\ smokers \in Smokers
    /\ offer \in SUBSET Ingredients

(*--- Liveness property (weak fairness) is expressed in the .cfg file, not here ---*)

====