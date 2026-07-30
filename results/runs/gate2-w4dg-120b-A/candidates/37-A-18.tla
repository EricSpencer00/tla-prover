---- MODULE CigaretteSmokers ----
EXTENDS Naturals, TLC

CONSTANTS
  Ingredients,
  Offers

VARIABLES
  smoking,
  offer

vars == <<smoking, offer>>

RECURSIVE SmokingCount(_)
SmokingCount(S) ==
  IF S = {} THEN 0
  ELSE LET i == CHOOSE x \in S : TRUE
       IN (IF smoking[i] THEN 1 ELSE 0) + SmokingCount(S \ {i})

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in (Offers \cup {{} })

\* At most one smoker is actively smoking at any time.
AtMostOne == SmokingCount(Ingredients) <= 1

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

\* A smoker whose ingredient completes the set takes the whole offer.
StartSmoking(i) ==
  /\ offer # {}
  /\ \E o \in Offers :
       /\ o = offer
       /\ (Ingredients \cup o) = Ingredients
       /\ i \in Ingredients \ o
  /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

\* The smoker stops and the dealer puts the next offer on the table.
StopSmoking(i) ==
  /\ offer = {}
  /\ smoking[i]
  /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next ==
  \/ \E i \in Ingredients : StartSmoking(i)
  \/ \E i \in Ingredients : StopSmoking(i)

Spec == Init /\ [][Next]_vars

\* Progress: the system keeps moving forward (smoking happens and stops).
SpecWithFairness == Spec /\ WF_vars(Next) /\ SF_vars(Next)

====