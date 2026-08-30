---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* smoking[i] is the smoking flag of the smoker who holds an infinite supply
\* of ingredient i; offer is either a valid offer (a subset missing one
\* ingredient) or empty, meaning someone is smoking.
TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ \E o \in Offers : offer = o

\* The dealer offers a full set of ingredients minus exactly one, and only
\* once the table is empty (no smoker currently smoking).
PlaceOffer(o) ==
  /\ offer = {}
  /\ o \in Offers
  /\ o # {}
  /\ Cardinality(Ingredients \ o) = 1
  /\ offer' = o
  /\ UNCHANGED smoking

StartSmoke(i) ==
  /\ offer # {}
  /\ ~smoking[i]
  /\ i \notin offer
  /\ \A j \in Ingredients : ~smoking[j]
  /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoke(i) ==
  /\ smoking[i]
  /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ UNCHANGED offer

Next ==
  \/ \E o \in Offers : PlaceOffer(o)
  \/ \E i \in Ingredients : StartSmoke(i) \/ StopSmoke(i)

Spec == Init /\ [][Next]_vars

\* At most one smoker is ever smoking: the smoking flags are pairwise
\* mutually exclusive, so two distinct smokers can never both be smoking.
AtMostOne ==
  \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

\* With a full table (a non-empty offer) some smoker can always start,
\* and with a smoker on the table that smoker can always stop, which is
\* strong fairness on both StartSmoke and StopSmoke.
Fairness ==
  /\ \A i \in Ingredients : SF_vars(StartSmoke(i))
  /\ \A i \in Ingredients : SF_vars(StopSmoke(i))

====