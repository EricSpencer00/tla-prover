---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoke, offer
vars == <<smoke, offer>>

\* The dealer's offer is always missing exactly one ingredient; a smoker
\* needs its own plus the offer to form the complete set.
Full == Cardinality(Ingredients)

TypeOK ==
  /\ sleep \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

Init ==
  /\ sleep = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : Cardinality(o) = Full - 1 /\ offer = o

\* Only a smoker whose own ingredient completes the full set may start.
CanSmoke(i) == i \notin offer /\ Cardinality(offer) = Full - 1

StartSmoke ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ CanSmoke(i)
       /\ sleep' = [sleep EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoke ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ sleep[i]
       /\ sleep' = [sleep EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : Cardinality(o) = Full - 1 /\ offer' = o

Next_ == StartSmoke \/ StopSmoke

Spec == Init /\ [][Next_]_vars
  /\ WF_vars(StopSmoke)

AtMostOne == Cardinality({i \in Ingredients : sleep[i]}) <= 1

====