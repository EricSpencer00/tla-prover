---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

\* Smokers sit in a ring; the ith smoker owns the ith ingredient from Ingredients.
\* The dealer offers a subset of ingredients missing exactly one, and a smoker
\* starts smoking only when their own infinite supply completes the full set. The
\* offer variable is cleared while someone smokes, so the offer and the smokers
\* together uniquely identify the single smoker currently lit.

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer, ring
vars == <<smoking, offer, ring>>

RECURSIVE SumOver(_)
SumOver(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN smoking[x] + SumOver(S \ {x})

\* Exactly one smoker being lit is checked using the pairwise-or form below;
\* the arithmetic sum form SumOver is convenient for a bounded-number bound.
OnlyOneSmokerLit == \A a, b \in Ingredients : (smoking[a] /\ smoking[b]) => (a = b)

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in (Offers \cup {{}})
  /\ cardinality(Ingredients) = cardinality(Offers) - 1
  /\ ONLYONESMOKERLIT

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o
  /\ ring = CHOOSE x \in Ingredients : TRUE

StartSmoking ==
  /\ offer # {}
  /\ ~smoking[ring]
  /\ \A i \in Ingredients : offer \cup {i} = Ingredients
  /\ smoking' = [smoking EXCEPT ![ring] = TRUE]
  /\ offer' = {}
  /\ UNCHANGED ring

StopSmoking ==
  /\ offer = {}
  /\ smoking[ring]
  /\ smoking' = [smoking EXCEPT ![ring] = FALSE]
  /\ \E o \in Offers : offer' = o
  /\ \E x \in Ingredients : ring' = x
  /\ UNCHANGED <<>>

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
        /\ WF_vars(StartSmoking)
        /\ WF_vars(StopSmoking)

AtMostOne == OnlyOneSmokerLit
====