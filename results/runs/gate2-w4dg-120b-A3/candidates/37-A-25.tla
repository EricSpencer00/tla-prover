---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer
vars == <<smoking, offer>>

\* A smoker who holds an infinite supply of an ingredient smokes when the
\* dealer's offer (together with that ingredient) forms the complete set.
Smoking == { i \in Ingredients : smoking[i] }

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ offer \in Offers

StartSmoking(i) ==
  /\ offer # {}
  /\ ~smoking[i]
  /\ i \cup offer = Ingredients
  /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking(i) ==
  /\ offer = {}
  /\ sleeping[i]
  /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ offer' \in Offers

Next == \E i \in Ingredients : StartSmoking(i) \/ StopSmoking(i)

Spec == Init /\ [][Next]_vars
  /\ \A i \in Ingredients : WF_vars(StartSmoking(i)) /\ WF_vars(StopSmoking(i))

AtMostOne ==
  /\ \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

====