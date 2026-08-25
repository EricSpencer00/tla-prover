---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

(*--------------------------------------------------------------------
  Type invariant: Smoking maps each ingredient to a Boolean.  Offer is
  either empty (a smoker is currently smoking) or one of the valid
  offers.
--------------------------------------------------------------------*)
TypeOK ==
  /\ Smoking \in [Ingredients -> BOOLEAN]
  /\ Offer \in ({} \cup Offers)

(*--------------------------------------------------------------------
  At most one smoker may be smoking at any time.
--------------------------------------------------------------------*)
AtMostOne ==
  \A i, j \in Ingredients :
    (Smoking[i] /\ Smoking[j]) => i = j

(*--------------------------------------------------------------------
  Initial state: no smoker is smoking, and the dealer places an
  initial offer nondeterministically from the set of valid offers.
--------------------------------------------------------------------*)
Init ==
  /\ Smoking = [i \in Ingredients |-> FALSE]
  /\ Offer    \in Offers

(*--------------------------------------------------------------------
  StartSmoking: when the table holds a non‑empty valid offer, the
  unique smoker whose ingredient is missing begins to smoke.  The
  offer is cleared.
--------------------------------------------------------------------*)
StartSmoking ==
  /\ Offer \in Offers
  /\ \A i \in Ingredients : Smoking[i] = FALSE   \* no smoker is currently smoking
  /\ \E i \in Ingredients :
        /\ i \notin Offer                      \* i is the missing ingredient
        /\ Smoking[i] = FALSE
        /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
        /\ Offer'   = {}

(*--------------------------------------------------------------------
  StopSmoking: when a smoker is smoking (Offer = {}), that smoker
  stops and the dealer places a new offer.
--------------------------------------------------------------------*)
StopSmoking ==
  /\ Offer = {}
  /\ \E i \in Ingredients :
        /\ Smoking[i] = TRUE
        /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
        /\ Offer'   \in Offers

(*--------------------------------------------------------------------
  Next-state relation.
--------------------------------------------------------------------*)
Next ==
  StartSmoking \/ StopSmoking

(*--------------------------------------------------------------------
  Specification: initial condition, temporal closure of Next, and
  weak fairness of Next.
--------------------------------------------------------------------*)
Spec ==
  Init /\ [][Next]_<<Smoking, Offer>> /\ WF_vars(<<Smoking, Offer>>)

=============================================================================