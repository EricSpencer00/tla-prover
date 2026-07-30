---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

NoSmoking == [i \in Ingredients |-> FALSE]

\* A smoker holds an infinite supply of exactly one ingredient; the offer on the
\* table is the set of the other two (when non-empty).
HasCompleteSet(i) == offer # {} /\ offer \cup {i} = Ingredients

Init ==
  /\ smoking = NoSmoking
  /\ offer \in Offers

StartSmoking(i) ==
  /\ offer # {}
  /\ HasCompleteSet(i)
  /\ smoking[i] = FALSE
  /\ \A k \in Ingredients : smoking[k] = FALSE
  /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking(i) ==
  /\ offer = {}
  /\ smoking[i] = TRUE
  /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next ==
  \E i \in Ingredients : StartSmoking(i) \/ StopSmoking(i)

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

AtMostOne ==
  \A i \in Ingredients : IF smoking[i] THEN \A k \in Ingredients : smoking[k]

Spec == Init /\ [][Next]_vars
        /\ \A i \in Ingredients : WF_vars(StartSmoking(i))
        /\ \A i \in Ingredients : WF_vars(StopSmoking(i))

====