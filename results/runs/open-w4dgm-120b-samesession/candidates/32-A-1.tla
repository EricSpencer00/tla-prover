---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures are referred to by their id 1..N; MeetingPlace is the shared
\* waiting slot (empty or holding one creature). ColorScheme records each
\* creature's current color and its own meeting count.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

VARIABLES ColorScheme, MeetingPlace, TotalMeetings

vars == <<ColorScheme, MeetingPlace, TotalMeetings>>

RECURSIVE SumOf(_, _)
SumOf(f, S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE
                    IN f[x] + SumOf(f, S \ {x})

TypeOK ==
  /\ ColorScheme \in [Creatures -> [color: Colors, count: 0..M]]
  /\ MeetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ TotalMeetings \in 0..M

Init ==
  /\ \E initCol \in [Creatures -> {"blue", "red", "yellow"}] :
       ColorScheme = [c \in Creatures |-> [color |-> initCol[c], count |-> 0]]
  /\ MeetingPlace = MeetingPlaceEmpty
  /\ TotalMeetings = 0

EnterMeetingPlace ==
  /\ MeetingPlace = MeetingPlaceEmpty
  /\ TotalMeetings < M
  /\ \E c \in Creatures :
       /\ ColorScheme[c].color # Faded
       /\ MeetingPlace' = c
  /\ UNCHANGED <<ColorScheme, TotalMeetings>>

FadeOut ==
  /\ MeetingPlace = MeetingPlaceEmpty
  /\ TotalMeetings >= M
  /\ \E c \in Creatures :
       /\ ColorScheme[c].color # Faded
       /\ ColorScheme' = [ColorScheme EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<MeetingPlace, TotalMeetings>>

\* The complement rule: identical colors stay; different colors both become
\* the third distinct color. The meeting place is emptied afterwards.
CompleteMeeting ==
  /\ MeetingPlace # MeetingPlaceEmpty
  /\ TotalMeetings < M
  /\ \E arr \in Creatures :
       /\ arr # MeetingPlace
       /\ ColorScheme[arr].color # Faded
       /\ LET ca == ColorScheme[MeetingPlace].color
              cb == ColorScheme[arr].color
              newcol == IF ca = cb THEN ca
                        ELSE [x \in Colors |-> Cardinality({x, ca, cb}) = 1][x]
          IN ColorScheme' = [ColorScheme EXCEPT
                               ![MeetingPlace] = [color |-> newcol,
                                                   count |-> @.count + 1],
                               ![arr] = [color |-> newcol,
                                         count |-> @.count + 1]]
       /\ MeetingPlace' = MeetingPlaceEmpty
  /\ TotalMeetings' = TotalMeetings + 1

Next == EnterMeetingPlace \/ FadeOut \/ CompleteMeeting

Spec == Init /\ [][Next]_vars

\* Each meeting touches two participants, so the summed per-creature
\* participation counts must reach exactly twice the number of meetings.
SumMet == (TotalMeetings = M) => (SumOf([c \in Creatures |-> ColorScheme[c].count], Creatures) = 2 * M)

====