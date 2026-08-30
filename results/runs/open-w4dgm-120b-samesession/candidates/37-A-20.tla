---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

HasA is a subset of Ingredients
SmokingAtoms == [a \in Ingredients |-> BOOLEAN]
Offer == Ingredients \cup {"none"}
None == "none"
Full == Ingredients

VARIABLES smoking, offer, atom

vars == <<smoking, offer, atom>>

Bump(x) == IF x < 3 THEN x + 1 ELSE 0

TypeOK ==
  /\ smoking \in SmokingAtoms
  /\ offer \in Offer
  /\ atom \in 0..3

Init ==
  /\ smoking = [a \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o
  /\ atom = 0

Start(a) ==
  /\ offer # None
  /\ ~smoking[a]
  /\ offer \cup {a} = Full
  /\ \A b \in Ingredients : ~smoking[b]
  /\ smoking' = [smoking EXCEPT ![a] = TRUE]
  /\ offer' = None
  /\ atom' = Bump(atom)

Stop(a) ==
  /\ smoking[a]
  /\ offer = None
  /\ smoking' = [smoking EXCEPT ![a] = FALSE]
  /\ \E o \in Offers : offer' = o
  /\ atom' = Bump(atom)

Next ==
  \E a \in Ingredients : Start(a) \/ Stop(a)

Spec == Init /\ [][Next]_vars

AtMostOne ==
  \A a1 \in Ingredients, a2 \in Ingredients :
    (smoking[a1] /\ smoking[a2]) => a1 = a2

====