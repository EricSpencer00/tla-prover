---- MODULE CigaretteSmokers ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT Ingredients \* The set of all ingredients, e.g. {"matches","paper","tobacco"}
CONSTANT Offers      \* The set of all valid offers (each missing exactly one ingredient)

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
FullSet == Ingredients

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES smoking, offer

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of smokers is identified by the ingredient they possess.
Smokers == Ingredients

\* The set of currently smoking smokers (should contain at most one element)
CurrentSmokers == { i \in Smokers : smoking[i] }

\* ----------------------------------------------------------------------
\* Type invariant (helps TLC check that variables stay within expected domains)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ smoking \in [Smokers -> BOOLEAN]
    /\ offer \in SUBSET Ingredients   \* empty or a valid offer

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ smoking = [i \in Smokers |-> FALSE]
    /\ offer \in Offers

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* A smoker can start smoking when the current offer together with his own
\* ingredient makes the full set. Exactly one such smoker may do so.
StartSmoking ==
    /\ offer # {}                                   \* there is an offer on the table
    /\ \E s \in Smokers :
          /\ ~smoking[s]                             \* the smoker is not already smoking
          /\ (offer \cup {s}) = FullSet              \* his ingredient completes the set
          /\ smoking' = [smoking EXCEPT ![s] = TRUE]
    /\ offer' = {}                                   \* the table becomes empty while he smokes
    /\ UNCHANGED << >>

StopSmoking ==
    /\ offer = {}                                    \* a smoker is currently smoking
    /\ \E s \in Smokers :
          /\ smoking[s]                              \* the smoker is the one that is smoking
          /\ smoking' = [smoking EXCEPT ![s] = FALSE]
    /\ offer' \in Offers                             \* dealer places a new offer
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<smoking, offer>>

\* ----------------------------------------------------------------------
\* Safety invariant: at most one smoker is smoking at any time
\* ----------------------------------------------------------------------
AtMostOne == Cardinality(CurrentSmokers) <= 1

\* ----------------------------------------------------------------------
\* Theorems (optional, can be used by TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []AtMostOne

====