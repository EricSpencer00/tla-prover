---- MODULE CigaretteSmokers ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Ingredients, Offers

(* --algorithm SmokingSimulation
variables
  smokers \* mapping each ingredient to its smoking status (TRUE = smoking)
  offer   \* current offer on the table (a subset of Ingredients or {})
variables
  smokers \in [Ingredients -> BOOLEAN];
  offer   \in Offers
end algorithm; *)

VARIABLES smokers, offer

\* The set of all possible offers is given by the constant Offers.
\* Each offer must be a subset of Ingredients missing exactly one ingredient.
\* The spec assumes that the .cfg file supplies a suitable definition of Offers.

(* Initial state: no smoker is smoking, and the dealer chooses an initial offer nondeterministically *)
Init ==
    /\ smokers = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

(* A smoker whose ingredient i completes the set (i.e., the current offer is Ingredients \ {i}) may start smoking *)
StartSmoking ==
    /\ offer # {}                     \* there is an offer on the table
    /\ \E i \in Ingredients :
          /\ offer = Ingredients \ {i}
          /\ smokers[i] = FALSE
    /\ \E i \in Ingredients :
          /\ offer = Ingredients \ {i}
          /\ smokers' = [smokers EXCEPT ![i] = TRUE]
    /\ offer' = {}                    \* the table is cleared while someone is smoking

(* When the table is empty, exactly one smoker is currently smoking; that smoker stops and the dealer places a new offer *)
StopSmoking ==
    /\ offer = {}                     \* a smoker is currently smoking
    /\ \E i \in Ingredients :
          /\ smokers[i] = TRUE
          /\ smokers' = [smokers EXCEPT ![i] = FALSE]
    /\ offer' \in Offers

(* No other state changes are allowed *)
Next ==
    \/ StartSmoking
    \/ StopSmoking

Spec == Init /\ [][Next]_<<smokers, offer>>

(* Type correctness invariant *)
TypeOK ==
    /\ smokers \in [Ingredients -> BOOLEAN]
    /\ offer \in (Offers \cup {{} })

(* Safety invariant: at most one smoker is smoking at any time *)
AtMostOne ==
    Cardinality({ i \in Ingredients : smokers[i] }) <= 1

=============================================================================