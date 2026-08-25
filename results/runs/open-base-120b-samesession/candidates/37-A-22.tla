---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

(*--------------------------------------------------------------------
  Type correctness invariant
--------------------------------------------------------------------*)
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {∅}

(*--------------------------------------------------------------------
  Initial state: no smoker is smoking; dealer places a nondeterministic
  valid offer.
--------------------------------------------------------------------*)
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ offer    \in Offers

(*--------------------------------------------------------------------
  Action: a smoker whose missing ingredient completes the set starts
  smoking.  The offer is cleared (set to ∅).
--------------------------------------------------------------------*)
StartSmoking ==
    /\ offer # ∅
    /\ \E i \in Ingredients :
          /\ i \notin offer               \* the ingredient missing from the offer
          /\ \A j \in Ingredients : (j # i => ~smoking[j])
          /\ smoking[i] = FALSE
    /\ LET i == CHOOSE j \in Ingredients :
                    j \notin offer /\ ~smoking[j] IN
         /\ smoking' = [smoking EXCEPT ![i] = TRUE]
         /\ offer'    = ∅

(*--------------------------------------------------------------------
  Action: the currently smoking smoker stops, and the dealer places a
  new nondeterministic offer.
--------------------------------------------------------------------*)
StopSmoking ==
    /\ offer = ∅
    /\ \E i \in Ingredients : smoking[i] = TRUE
    /\ LET i == CHOOSE j \in Ingredients : smoking[j] = TRUE IN
         /\ smoking' = [smoking EXCEPT ![i] = FALSE]
         /\ offer'    \in Offers

Next ==
    \/ StartSmoking
    \/ StopSmoking

(*--------------------------------------------------------------------
  Specification: initial condition, temporal closure of Next, and weak
  fairness for both actions to guarantee progress.
--------------------------------------------------------------------*)
Spec ==
    Init
    /\ [][Next]_<<smoking, offer>>
    /\ WF_<<smoking, offer>>(StartSmoking)
    /\ WF_<<smoking, offer>>(StopSmoking)

(*--------------------------------------------------------------------
  Safety invariant: at most one smoker is smoking at any time.
--------------------------------------------------------------------*)
AtMostOne ==
    Cardinality({ i \in Ingredients : smoking[i] }) <= 1

====