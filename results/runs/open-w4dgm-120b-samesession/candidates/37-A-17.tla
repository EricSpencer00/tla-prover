---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

\* The smoker who holds an infinite supply of i (a single ingredient from the
\* full set) is smoking iff Smoking[i] = TRUE; the dealer's offer is the
\* current non-empty Offer on the table, or {} while someone smokes.
VARIABLES Smoking, Offer

vars == <<Smoking, Offer>>

\* SAFETY PROPERTY: the pairwise intersection of any two smokers' smoking
\* states is empty, i.e. no two distinct smokers are ever both smoking.
AtMostOneSmoking == \A i, j \in Ingredients : (Smoking[i] /\ Smoking[j]) => i = j

TypeOK ==
  /\ Smoking \in [Ingredients -> BOOLEAN]
  /\ Offer \in Offers \cup {{}}

Init ==
  /\ Smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : Offer = o

\* Starting a smoke clears the offer (tables go empty while a smoker puffs).
StartSmoking(i) ==
  /\ Offer # {}
  /\ \E j \in Ingredients : Offer \cup {j} = Ingredients
  /\ i \in Offer
  /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
  /\ Offer' = {}

StopSmoking(i) ==
  /\ Smoking[i]
  /\ \E o \in Offers : Offer' = o
  /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]

Next ==
  \E i \in Ingredients : StartSmoking(i) \/ StopSmoking(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in Ingredients : SF_vars(StartSmoking(i)) /\ SF_vars(StopSmoking(i))

\* LIVENESS PROPERTY: every smoker gets its turn to smoke.
EverySmokerSmokes == \A i \in Ingredients : <>(Smoking[i] = TRUE)

====