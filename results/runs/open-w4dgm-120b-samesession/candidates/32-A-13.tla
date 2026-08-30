---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* color is the creature's current hue or the faded terminal state;
\* cnt is that creature's individual meeting count.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
\* The complement rule: with two colors it returns the third one.
Third(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE IF {c1, c2} = {"blue", "red"} THEN "yellow"
  ELSE IF {c1, c2} = {"red", "yellow"} THEN "blue"
  ELSE "red"

VARIABLES status, waiting, total
vars == <<status, waiting, total>>

RECURSIVE Met(_)
Met(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN status[x].cnt + Met(S \ {x})

TypeOK ==
  /\ status \in [Creatures -> [color : Colors, cnt : 0..M]]
  /\ waiting \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in 0..M

Init ==
  /\ status \in [Creatures -> [color : {"blue", "red", "yellow"}, cnt : 0]]
  /\ waiting = MeetingPlaceEmpty
  /\ total = 0

Enter(c) ==
  /\ waiting = MeetingPlaceEmpty
  /\ status[c].color # Faded
  /\ total < M
  /\ waiting' = c
  /\ UNCHANGED <<status, total>>

Fade(c) ==
  /\ waiting = MeetingPlaceEmpty
  /\ status[c].color # Faded
  /\ total = M
  /\ status' = [status EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<waiting, total>>

Meet(c) ==
  /\ waiting # MeetingPlaceEmpty
  /\ waiting # c
  /\ status[c].color # Faded
  /\ LET newcol == Third(status[c].color, status[waiting].color) IN
       /\ status' = [status EXCEPT ![c] = [color |-> newcol, cnt |-> @.cnt + 1],
                                   ![waiting] = [color |-> newcol, cnt |-> @.cnt + 1]]
  /\ total' = total + 1
  /\ waiting' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : Enter(c)
  \/ \E c \in Creatures : Fade(c)
  \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

\* Every meeting has exactly two participants, so at the meeting ceiling the
\* summed individual counts reach twice the number of meetings.
SumMet == total = M => Met(Creatures) = 2 * M
====