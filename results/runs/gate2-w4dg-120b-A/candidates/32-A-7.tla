---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creature identifiers are the numbers 1..N.
Creatures == 1..N

Colors == {"blue", "red", "yellow", Faded}

VARIABLES color, met, place, total
vars == <<color, met, place, total>>

RECURSIVE SumMetOver(_)
SumMetOver(S) == IF S = {} THEN 0
                  ELSE LET x == CHOOSE y \in S : TRUE IN met[x] + SumMetOver(S \ {x})

TypeOK ==
  /\ color \in [Creatures -> Colors]
  /\ met \in [Creatures -> 0..M]
  /\ place \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in 0..M

Init ==
  /\ \E c \in [Creatures -> Colors \ {"Faded"}] :
       \E k \in [Creatures -> 0..M] :
         /\ color = c
         /\ met = k
  /\ place = MeetingPlaceEmpty
  /\ total = 0

\* A creature enters the meeting place if it is empty and the meetings have not run out.
Enter(c) ==
  /\ place = MeetingPlaceEmpty
  /\ total < M
  /\ color[c] # Faded
  /\ place' = c
  /\ UNCHANGED <<color, met, total>>

\* Once meetings have run out, a creature that tries to enter simply fades.
Fade(c) ==
  /\ place = MeetingPlaceEmpty
  /\ total = M
  /\ color[c] # Faded
  /\ color' = [color EXCEPT ![c] = Faded]
  /\ UNCHANGED <<met, place, total>>

\* Two different creatures at the meeting place exchange colors according to the rule.
Meet(c) ==
  /\ place # MeetingPlaceEmpty
  /\ c # place
  /\ met[place] < M
  /\ total' = total + 1
  /\ met' = [met EXCEPT ![place] = met[place] + 1, ![c] = met[c] + 1]
  /\ IF color[place] = color[c] THEN
       color' = color
     ELSE
       \E x \in Colors : color' = [color EXCEPT ![place] = x, ![c] = x]
  /\ place' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : Enter(c)
  \/ \E c \in Creatures : Fade(c)
  \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

\* When meetings are exhausted, every creature has exhausted its own meeting count.
SumMet == (total = M) => (SumMetOver(Creatures) = 2 * M)

====