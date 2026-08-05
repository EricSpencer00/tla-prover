---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

VARIABLES phase, meetingPlace, totalMeetings

vars == <<phase, meetingPlace, totalMeetings>>

\* Each creature tracks its own meeting count; the global counter double-counts
\* (every meeting contributes two participants) as checked by the invariant.
Creatures == 0..(N - 1)
Colors == {"blue", "red", "yellow", Faded}
ColorOf(c) == phase[c][1]
CountOf(c) == phase[c][2]

Third(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE LET s == {c1, c2} IN CHOOSE y \in Colors : y \notin s

TypeOK ==
  /\ phase \in [Creatures -> (Colors \X (0..M))]
  /\ meetingPlace \in (Creatures \cup {MeetingPlaceEmpty})
  /\ totalMeetings \in 0..M

Init ==
  /\ phase = [c \in Creatures |-> ({CHOOSE col \in Colors : col # Faded}, 0)]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

EnterMeetingPlace(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ ColorOf(c) # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED <<phase, totalMeetings>>

FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ ColorOf(c) # Faded
  /\ phase' = [phase EXCEPT ![c] = <<Faded, @.2>>]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

MeetAndMutate(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ ColorOf(c) # Faded
  /\ ColorOf(meetingPlace) # Faded
  /\ LET newcol == Third(ColorOf(c), ColorOf(meetingPlace)) IN
       phase' = [phase EXCEPT ![c] = <<newcol, CountOf(c) + 1>>, ![meetingPlace] = <<newcol, CountOf(meetingPlace) + 1>>]
  /\ totalMeetings' = totalMeetings + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next == \E c \in Creatures : EnterMeetingPlace(c) \/ FadeOut(c) \/ MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet ==
  /\ totalMeetings = M
  /\ LET f[S \in SUBSET Creatures] ==
        IF S = {} THEN 0
        ELSE LET c == CHOOSE x \in S : TRUE IN CountOf(c) + f[S \ {c}]
     IN f[Creatures] = 2 * M

====