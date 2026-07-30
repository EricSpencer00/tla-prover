---- MODULE Chameneos ----
EXTENDS Integers

CONSTANTS N, M, Faded, MeetingPlaceEmpty

CREATURES == 0 .. (N - 1)
Colors == {"blue", "red", "yellow", Faded}
NonFadedColors == {"blue", "red", "yellow"}

\* The per-creature mapping is a record: each creature id maps to <<color, ownCount>>.
VARIABLES cmap, waiting, metTotal

vars == <<cmap, waiting, metTotal>>

TypeOK ==
  /\ cmap \in [CREATURES -> [color : Colors, ownCount : 0 .. M]]
  /\ waiting \in CREATURES \union {MeetingPlaceEmpty}
  /\ metTotal \in 0 .. M

RECURSIVE SumCounts(_)
SumCounts(S) ==
  IF S = {} THEN 0
  ELSE LET c == CHOOSE x \in S : TRUE IN cmap[c].ownCount + SumCounts(S \ {c})

SumMet == SumCounts(CREATURES)

\* The complement rule: if two colors differ, both become the third (missing) one;
\* if they are the same, both stay that color.
Complement(a, b) ==
  IF a = b THEN a
  ELSE LET missing == {"blue", "red", "yellow"} \ {a, b} IN CHOOSE x \in missing : TRUE

Init ==
  /\ cmap \in [CREATURES -> [color : NonFadedColors, ownCount : 0]]
  /\ waiting = MeetingPlaceEmpty
  /\ metTotal = 0

Enter ==
  /\ waiting = MeetingPlaceEmpty
  /\ metTotal < M
  /\ \E c \in CREATURES :
       /\ cmap[c].color # Faded
       /\ waiting' = c
  /\ UNCHANGED <<cmap, metTotal>>

FadeOut ==
  /\ waiting = MeetingPlaceEmpty
  /\ metTotal >= M
  /\ \E c \in CREATURES :
       /\ cmap[c].color # Faded
       /\ cmap' = [cmap EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<waiting, metTotal>>

Meet ==
  /\ waiting # MeetingPlaceEmpty
  /\ \E c \in CREATURES :
       /\ cmap[c].color # Faded
       /\ c # waiting
       /\ cmap' = [x \in CREATURES |->
                    IF x = c /\ x = waiting THEN cmap[x]
                    ELSE IF x = c \/ x = waiting
                    THEN [color |-> Complement(cmap[c].color, cmap[waiting].color), ownCount |-> cmap[x].ownCount + 1]
                    ELSE cmap[x]]
       /\ metTotal' = metTotal + 1
       /\ waiting' = MeetingPlaceEmpty
  /\ UNCHANGED << >>  \* all other vars already accounted for

Next == Enter \/ FadeOut \/ Meet

Spec == Init /\ [][Next]_vars

\* Safety: once the global meeting counter reaches its maximum, the sum of all
\* per-creature meeting tallies must account for exactly two participants per
\* meeting (counted from both sides).
SumMetMax == metTotal = M => SumMet = 2 * M

====