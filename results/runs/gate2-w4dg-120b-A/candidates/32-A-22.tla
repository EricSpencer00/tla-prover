---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

VARIABLES traits, meetingPlace, totalMeetings

vars == <<traits, meetingPlace, totalMeetings>>

Creatures == 1 .. N
Colors == {"blue", "red", "yellow"}

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

ComplementColor(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE LET unused == CHOOSE z \in Colors : z # c1 /\ z # c2 IN unused

TypeOK ==
  /\ traits \in [Creatures -> [color : Colors \cup {Faded}, attended : 0..M]]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ \E c \in [Creatures -> Colors] : traits = [n \in Creatures |-> [color |-> c[n], attended |-> 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

Enter(n) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ traits[n].color # Faded
  /\ totalMeetings < M
  /\ meetingPlace' = n
  /\ UNCHANGED <<traits, totalMeetings>>

FadeOut(n) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ traits[n].color # Faded
  /\ totalMeetings = M
  /\ traits' = [traits EXCEPT ![n].color = Faded]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

MeetAndMutate(n) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # n
  /\ traits[n].color # Faded
  /\ traits[meetingPlace].color # Faded
  /\ LET nc == ComplementColor(traits[n].color, traits[meetingPlace].color) IN
       /\ traits' = [traits EXCEPT ![n].color = nc, ![meetingPlace].color = nc,
                     ![n].attended = @ + 1, ![meetingPlace].attended = @ + 1]
  /\ totalMeetings' = totalMeetings + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ \E n \in Creatures : Enter(n)
  \/ \E n \in Creatures : FadeOut(n)
  \/ \E n \in Creatures : MeetAndMutate(n)

Spec == Init /\ [][Next]_vars

SumMet ==
  (totalMeetings = M) => (SumOf([n \in Creatures |-> traits[n].attended], Creatures) = 2 * M)

====