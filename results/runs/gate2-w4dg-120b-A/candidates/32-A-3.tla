---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

\* Chameneos meet pairwise at a central meeting place; a meeting counts as an
\* atomic swap of both participants' colors. The place closes once the total
\* meeting budget is spent and any creature trying to enter fades out.

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME /\ N \in Nat /\ N > 0
       /\ M \in Nat /\ M > 0
       /\ Faded \notin {"blue", "red", "yellow"}

Creatures == 1 .. N

VARIABLES color, place, totalMet

vars == << color, place, totalMet >>

TypeOK ==
  /\ color \in [Creatures -> [c : {"blue", "red", "yellow", Faded}, m : 0 .. M]]
  /\ place \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMet \in 0 .. M

SumMet ==
  LET add[f \in SUBSET Creatures] ==
        IF f = {} THEN 0
        ELSE LET x == CHOOSE y \in f : TRUE IN color[x].m + add[f \ {x}]
  IN add[Creatures]

\* The complement rule: a pair of equal colors stays put; a mixed pair both
\* adopt the third, unheld color.
Complement(x, y) ==
  IF x = y THEN x
  ELSE IF (x = "blue" /\ y = "red") \/ (x = "red" /\ y = "blue") THEN "yellow"
  ELSE IF (x = "blue" /\ y = "yellow") \/ (x = "yellow" /\ y = "blue") THEN "red"
  ELSE "blue"

\* Each creature's meeting count rises by exactly one per meeting it joins.
\* Because a meeting needs two participants, the global budget M must be
\* accounted for twice over the whole system: the sum of individual met counts
\* must equal 2 * M once the budget is spent.
MetBudgetFitsTwoParticipants == (totalMet = M) => (SumMet = 2 * M)

Init ==
  /\ color \in [Creatures -> [c : {"blue", "red", "yellow"}, m : 0]]
  /\ place = MeetingPlaceEmpty
  /\ totalMet = 0

\* A creature enters the meeting place only while the budget is unspent and it
\* has not faded.
EnterPlace(x) ==
  /\ place = MeetingPlaceEmpty
  /\ totalMet < M
  /\ color[x].c # Faded
  /\ place' = x
  /\ UNCHANGED << color, totalMet >>

\* When the budget is spent, a creature that shows up fades out instead of
\* entering — this is the irreversible step that keeps the system alive.
FadeOut(x) ==
  /\ place = MeetingPlaceEmpty
  /\ totalMet = M
  /\ color[x].c # Faded
  /\ color' = [color EXCEPT ![x].c = Faded]
  /\ UNCHANGED << place, totalMet >>

\* Two creatures in the meeting place swap colors and both get a meeting credit.
MeetAndSwap(x) ==
  /\ place # MeetingPlaceEmpty
  /\ x # place
  /\ color[x].c # Faded
  /\ color[place].c # Faded
  /\ LET newcol == Complement(color[x].c, color[place].c) IN
       /\ color' = [color EXCEPT ![x].c = newcol, ![place].c = newcol]
  /\ color' = [color' EXCEPT ![x].m = color[x].m + 1, ![place].m = color[place].m + 1]
  /\ totalMet' = totalMet + 1
  /\ place' = MeetingPlaceEmpty

Next ==
  \/ \E x \in Creatures : EnterPlace(x) \/ FadeOut(x) \/ MeetAndSwap(x)

Spec == Init /\ [][Next]_vars

====