---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N > 0
ASSUME M \in Nat /\ M > 0

Creatures == 1 .. N
Colors == {"blue", "red", "yellow", Faded}

VARIABLES cmap, meetingPlace, totalMeetings

vars == <<cmap, meetingPlace, totalMeetings>>

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

TypeOK ==
  /\ cmap \in [Creatures -> [color: Colors, met: 0 .. M]]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0 .. M

Init ==
  /\ cmap \in [Creatures -> [color: {"blue", "red", "yellow"}, met: 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

ThirdColor(a, b) ==
  CASE
    /\ a = b     -> a
    /\ {a, b} = {"blue", "red"}     -> "yellow"
    /\ {a, b} = {"blue", "yellow"}  -> "red"
    /\ {a, b} = {"red", "yellow"}   -> "blue"
    /\ OTHER     -> a

Enter(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ cmap[c].color # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED <<cmap, totalMeetings>>

FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ cmap[c].color # Faded
  /\ cmap' = [cmap EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

MeetMutate(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ c # meetingPlace
  /\ cmap[meetingPlace].color # Faded
  /\ cmap[c].color # Faded
  /\ totalMeetings < M
  /\ LET newc == ThirdColor(cmap[c].color, cmap[meetingPlace].color) IN
       cmap' = [cmap EXCEPT
                 ![c].color = newc,
                 ![c].met = @ + 1,
                 ![meetingPlace].color = newc,
                 ![meetingPlace].met = @ + 1]
  /\ totalMeetings' = totalMeetings + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \E c \in Creatures : Enter(c) \/ FadeOut(c) \/ MeetMutate(c)

Spec == Init /\ [][Next]_vars

SumMet == totalMeetings = M => SumOver([c \in Creatures |-> cmap[c].met], Creatures) = 2 * M
====