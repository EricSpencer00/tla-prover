---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Ingredients, \* the set of all possible ingredients (e.g., {"matches","paper","tobacco"})
    Offers      \* the set of all allowed offers (each a subset of Ingredients missing exactly one)

VARIABLES
    smokers,   \* mapping each ingredient to a Boolean indicating if its smoker is currently smoking
    offer      \* the current offer on the table; either a subset of Ingredients (missing exactly one) or {} when a smoker is smoking

(* --type definitions ------------------------------------------------------- *)

SMOKERS == [i \in Ingredients |-> BOOLEAN]

\* An offer is either empty (meaning a smoker is currently smoking) or a non‑empty
\* subset of Ingredients that is missing exactly one ingredient.
ValidOffer == { s \in SUBSET Ingredients : 
                 \E missing \in Ingredients : missing \notin s /\ Cardinality(s) = Cardinality(Ingredients) - 1 }

\* Type correctness predicate
TypeOK ==
    /\ smokers \in SMOKERS
    /\ (offer = {} \/ offer \in Offers)

(* --initial state----------------------------------------------------------- *)

Init ==
    /\ smokers = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

(* --actions----------------------------------------------------------------- *)

StartSmoking ==
    /\ offer # {}                                 \* there is an offer on the table
    /\ \E i \in Ingredients :
           /\ i \notin offer                     \* the missing ingredient belongs to the smoker i
           /\ smokers[i] = FALSE                 \* i is not already smoking
           /\ smokers' = [smokers EXCEPT ![i] = TRUE]
    /\ offer' = {}                               \* the table becomes empty while the smoker smokes

StopSmoking ==
    /\ offer = {}                                 \* a smoker is currently smoking
    /\ \E i \in Ingredients :
           /\ smokers[i] = TRUE                  \* exactly one smoker is smoking
           /\ smokers' = [smokers EXCEPT ![i] = FALSE]
    /\ offer' \in Offers                         \* dealer places a new (valid) offer

Next ==
    \/ StartSmoking
    \/ StopSmoking

(* --specification----------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<smokers, offer>>

(* --derived predicates------------------------------------------------------- *)

AtMostOne ==
    Cardinality({ i \in Ingredients : smokers[i] }) <= 1

=============================================================================