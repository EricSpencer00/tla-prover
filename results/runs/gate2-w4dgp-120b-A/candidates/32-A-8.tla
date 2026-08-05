---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures are identified as the natural numbers 1, 2, ..., N.
Creatures == 1..N

Colors == {"blue", "red", "yellow", Faded}

\* The complement rule: two creatures meeting.
\* Same color: no change; different colors: both adopt the third.
Complement(c, c) == c
Complement(c1, c2) == LET s == {c1, c2} IN CHOOSE c3 \in Colors \ {Faded} : s \cup {c3} = Colors \ {Faded}

VARIABLES colorAndMet, meetingPlace, totalMet

vars == <<colorAndMet, meetingPlace, totalMet>>

MetTotal == LET f[T \in SUBSET Creatures] ==
                 IF T = {} THEN 0
                 ELSE LET x == CHOOSE y \in T : TRUE IN colorAndMet[x][2] + f[T \ {x}]
             IN f[Creatures]

TypeOK ==
  /\ colorAndMet \in [Creatures -> (Colors \times (0..M))]
  /\ meetingPlace \in (Creatures \cup {MeetingPlaceEmpty})
  /\ totalMet \in 0..M

Init ==
  /\ colorAndMet \in [Creatures -> (Colors \ {Faded} \times {0})]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet = 0

EnterMeetingPlace(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ colorAndMet[c][1] # Faded
  /\ totalMet < M
  /\ meetingPlace' = c
  /\ UNCHANGED <<colorAndMet, totalMet>>

FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet >= M
  /\ colorAndMet[c][1] # Faded
  /\ colorAndMet' = [colorAndMet EXCEPT ![c] = <<Faded, colorAndMet[c][2]>>]
  /\ UNCHANGED <<meetingPlace, totalMet>>

\* Two distinct creatures meet and both change color; both are counted.
MeetAndMutate(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ totalMet < M
  /\ LET c1 == meetingPlace
         newCol == Complement(colorAndMet[c][1], colorAndMet[c1][1])
     IN colorAndMet' = [colorAndMet EXCEPT
                           ![c] = <<newCol, colorAndMet[c][2] + 1>>,
                           ![c1] = <<newCol, colorAndMet[c1][2] + 1>>]
  /\ totalMet' = totalMet + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures: EnterMeetingPlace(c)
  \/ \E c \in Creatures: FadeOut(c)
  \/ \E c \in Creatures: MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet == (totalMet = M) => (MetTotal = 2 * M)

====