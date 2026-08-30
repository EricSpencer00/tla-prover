---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

\* smokers[c] is the smoking flag of the smoker who holds infinite supply of ingredient c
VARIABLES smokers, offer

vars == <<smokers, offer>>

TypeOK ==
  /\ smokers \in [Ingredients -> BOOLEAN]
  /\ offer \in (SUBSET Ingredients) \union {"empty"}

Init ==
  /\ smokers = [c \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

AtMostOne ==
  \A c1 \in Ingredients, c2 \in Ingredients :
    (smokers[c1] /\ smokers[c2]) => c1 = c2

StartSmoking(c) ==
  /\ offer # "empty"
  /\ ~smokers[c]
  /\ offer \union {c} = Ingredients
  /\ smokers' = [smokers EXCEPT ![c] = TRUE]
  /\ offer' = "empty"

StopSmoking(c) ==
  /\ smokers[c]
  /\ smokers' = [smokers EXCEPT ![c] = FALSE]
  \/ \E o \in Offers : offer' = o

Next ==
  \E c \in Ingredients : StartSmoking(c) \/ StopSmoking(c)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Ingredients : WF_vars(StartSmoking(c))
  /\ \A c \in Ingredients : WF_vars(StopSmoking(c))

\* The dealer only places valid offers, each missing exactly one ingredient
OffersValid == \A o \in Offers : Cardinality(Ingredients \ o) = 1
====