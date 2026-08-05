---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

CREATURES == 1 .. N
COLORS == {"blue", "red", "yellow", Faded}
Other(c, x) == LET S == {c, x} IN CHOOSE y \in COLORS : y \notin S

VARIABLES state, meetingPlace, totalMeetings
vars == <<state, meetingPlace, totalMeetings>>

TypeOK ==
  /\ state \in [CREATURES -> (COLORS \ {Faded}) \X (0 .. M)]
  /\ meetingPlace \in CREATURES \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0 .. M

Init ==
  /\ state = [c \in CREATURES |-> <<CHOOSE cl \in { "blue", "red", "yellow" } : TRUE, 0>>]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

Enter(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ state[c][1] # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED <<state, totalMeetings>>

FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ state[c][1] # Faded
  /\ state' = [state EXCEPT ![c] = <<Faded, state[c][2>>]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* Two different creatures exchange colors determined by the complement rule,
\* each counts this as its own meeting, and the meeting place is emptied.
Meet(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ state[c][1] # Faded
  /\ state[meetingPlace][1] # Faded
  /\ LET newc == IF state[c][1] = state[meetingPlace][1]
                 THEN state[c][1]
                 ELSE Other(state[c][1], state[meetingPlace][1])
             nc == state[meetingPlace]
         IN
           /\ state' = [state EXCEPT ![c] = <<newc, @ [2] + 1>>, ![meetingPlace] = <<newc, nc[2] + 1>>]
           /\ totalMeetings' = totalMeetings + 1
           /\ meetingPlace' = MeetingPlaceEmpty

Next == \E c \in CREATURES : Enter(c) \/ FadeOut(c) \/ Meet(c)

Spec == Init /\ [][Next]_vars

\* At the meeting ceiling, individual meeting counts sum up to twice that ceiling:
\* each meeting logged twice, once per participant.
SumMet ==
  (totalMeetings = M) =>
   (state[1][2] + state[2][2] + (IF N >= 3 THEN state[3][2] ELSE 0) +
    (IF N >= 4 THEN state[4][2] ELSE 0) + (IF N >= 5 THEN state[5][2] ELSE 0) = 2 * M)

====