---- MODULE CigaretteSmokers ----
(***************************************************************************)
(* The cigarette smokers problem (Patil 1971).  A dealer places a subset   *)
(* of ingredients on the table; each smoker owns an infinite supply of    *)
(* exactly one ingredient.  A smoker may smoke when the dealer's offer    *)
(* plus the smoker's own ingredient completes the full set.  At most one  *)
(* smoker smokes at any time; the dealer waits for the smoker to finish   *)
(* before placing a new offer.                                            *)
(*                                                                         *)
(* Safety: at most one smoker is smoking.                                 *)
(* Liveness: weak fairness on the next-state relation.                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

ASSUME \E o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1

VARIABLES smoking

vars == << smoking >>

\* smoking[i] = TRUE iff the smoker who owns ingredient i is currently
\* smoking.  Exactly one smoker may be smoking at any time.
Init == smoking = [i \in Ingredients |-> FALSE]

\* Start smoking: the dealer's offer is non-empty; exactly one smoker whose
\* ingredient completes the full set begins smoking; the offer is cleared.
StartSmoking == /\ \E o \in Offers : \E i \in Ingredients :
                  /\ o \cup {i} = Ingredients
                  /\ smoking[i] = FALSE
                  /\ \A j \in Ingredients \ {i} : smoking[j] = FALSE
                  /\ smoking' = [smoking EXCEPT ![i] = TRUE]

\* Stop smoking: the single currently-smoking smoker stops; the dealer
\* places a new offer chosen nondeterministically from the set of valid
\* offers.
StopSmoking == /\ \E i \in Ingredients : smoking[i] = TRUE
               /\ \E o \in Offers : o \cup {i} = Ingredients
               /\ smoking' = [j \in Ingredients |-> FALSE]

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

\* Strong safety: at most one smoker is smoking at any time.
AtMostOne == Cardinality({i \in Ingredients : smoking[i]}) <= 1

\* Strong safety: the smoking flag is always a Boolean.
TypeOK == /\ smoking \in Ingredients -> BOOLEAN
          /\ AtMostOne
====