---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANT Ingredients, Offers

VARIABLES Smokers, Offer

(*--------------------------------------------------------------------
  Type invariant
--------------------------------------------------------------------*)
TypeOK ==
    /\ Smokers \in [Ingredients -> BOOLEAN]
    /\ Offer \in SUBSET Ingredients

(*--------------------------------------------------------------------
  Initial state: no smoker is smoking, dealer places a valid offer
--------------------------------------------------------------------*)
Init ==
    /\ Smokers = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

(*--------------------------------------------------------------------
  Action: a smoker starts smoking
  The current offer together with the smoker's own ingredient forms the
  complete set of Ingredients. The offer is cleared (set to {}).
--------------------------------------------------------------------*)
Start ==
    /\ Offer # {}
    /\ \E i \in Ingredients :
          /\ ~Smokers[i]
          /\ Offer \cup {i} = Ingredients
          /\ Smokers' = [Smokers EXCEPT ![i] = TRUE]
          /\ Offer' = {}

(*--------------------------------------------------------------------
  Action: the currently smoking smoker stops and the dealer offers again
--------------------------------------------------------------------*)
Stop ==
    /\ Offer = {}
    /\ \E i \in Ingredients :
          /\ Smokers[i]
          /\ Smokers' = [Smokers EXCEPT ![i] = FALSE]
          /\ Offer' \in Offers

Next == Start \/ Stop

(*--------------------------------------------------------------------
  Safety property: at most one smoker is smoking
--------------------------------------------------------------------*)
AtMostOne ==
    \A i, j \in Ingredients :
        (Smokers[i] /\ Smokers[j]) => i = j

(*--------------------------------------------------------------------
  Specification: init, always next, weak fairness of Next
--------------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<Smokers, Offer>> /\ WF_<<Smokers, Offer>>(Next)

====