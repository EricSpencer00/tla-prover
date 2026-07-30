---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creature i currently sits in a meeting place slot (or not) and is recorded
\* as waiting there by the meetingPlace variable below.
\* Its own register records its color and its personal meeting tally.
Creatures == 0..(N-1)
Colors == {"blue", "red", "yellow"}
Database == [color : Colors \cup {Faded}, count : 0..M]

VARIABLES database, meetingPlace, totalMeetings

vars == <<database, meetingPlace, totalMeetings>>

RECURSIVE TallyOf(_)
TallyOf(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE e \in S : TRUE IN database[x].count + TallyOf(S \ {x})

TypeOK ==
  /\ database \in [Creatures -> Database]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init == 
  /\ database = [i \in Creatures |-> [color |-> CHOOSE c \in Colors : TRUE, count |-> 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

Enter(i) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ database[i].color # Faded
  /\ totalMeetings < M
  /\ meetingPlace' = i
  /\ UNCHANGED <<database, totalMeetings>>

FadeOut(i) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ database[i].color # Faded
  /\ totalMeetings >= M
  /\ database' = [database EXCEPT ![i].color = Faded]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

Complement(c1, c2) == 
  IF c1 = c2 THEN c1
  ELSE LET third == CHOOSE c \in Colors : (c # c1) /\ (c # c2) IN third

Meet(i) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # i
  /\ database[i].color # Faded
  /\ database[meetingPlace].color # Faded
  /\ totalMeetings < M
  /\ LET newc == Complement(database[i].color, database[meetingPlace].color) IN
       /\ database' = [database EXCEPT ![i].color = newc, ![meetingPlace].color = newc,
                                   ![i].count = @ + 1, ![meetingPlace].count = @@ + 1]
  /\ meetingPlace' = MeetingPlaceEmpty
  /\ totalMeetings' = totalMeetings + 1

Next ==
  \/ \E i \in Creatures : Enter(i)
  \/ \E i \in Creatures : FadeOut(i)
  \/ \E i \in Creatures : Meet(i)

Spec == Init /\ [][Next]_vars

SumMet == (totalMeetings = M) => (TallyOf(Creatures) = 2 * M)

====