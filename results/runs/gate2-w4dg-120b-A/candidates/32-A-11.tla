---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures are identified by numbers 1..N. Each creature's state is a pair
\* of its current color and the number of meetings it has participated in.
ASSUME N \in Nat /\ N > 0
ASSUME M \in Nat /\ M > 0
Colours == {"blue", "red", "yellow"}
Complements(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE CHOOSE c \in Colours : c # c1 /\ c # c2

VARIABLES creature, meetingPlace, totalMeetings

Vars == <<creature, meetingPlace, totalMeetings>>

% Sum of a function over the creature domain 1..N.
SumOver(f) == LET g[i \in 0..N] ==
                  IF i = 0 THEN 0
                  ELSE g[i-1] + f[i]
              IN g[N]

TypeOK ==
  /\ creature \in [1..N -> (Colours \cup {Faded}) \X (0..(2 * M))]
  /\ meetingPlace \in (1..N) \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ creature = [c \in 1..N |-> <<CHOOSE col \in Colours : TRUE, 0>>]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

EnterMeetingPlace(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ creature[c][1] # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED <<creature, totalMeetings>>

FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ creature[c][1] # Faded
  /\ creature' = [creature EXCEPT ![c] = <<Faded, @ [2]>>]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

MeetAndMutate(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ meetingPlace' = MeetingPlaceEmpty
  /\ creature' = [creature EXCEPT ![c] = <<Complements(@[1], creature[meetingPlace][1]), @ [2] + 1>,
                                 ![meetingPlace] = <<Complements(@[1], creature[c][1]), @ [2] + 1>>]
  /\ totalMeetings' = totalMeetings + 1

Next ==
  \/ \E c \in 1..N : EnterMeetingPlace(c)
  \/ \E c \in 1..N : FadeOut(c)
  \/ \E c \in 1..N : MeetAndMutate(c)

Spec == Init /\ [][Next]_Vars

SumMet ==
  (totalMeetings = M) => (SumOver([c \in 1..N |-> creature[c][2]]) = 2 * M)

====