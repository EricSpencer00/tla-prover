---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 0 .. (N - 1)
Colors == {"blue", "red", "yellow", Faded}
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE LET r == {"blue", "red", "yellow"} \ {c1, c2} IN CHOOSE c \in r : TRUE

VARIABLES state, meetingPlace, totalMeetings

Parts == {"color", "met"}

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

TypeOK ==
    /\ state \in [Creatures -> [color: Colors, met: Nat]]
    /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0..M

Init ==
    /\ state = [c \in Creatures |-> [color |-> CHOOSE cl \in {"blue", "red", "yellow"} : TRUE, met |-> 0]]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0

EnterMall ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ \E c \in Creatures :
         /\ state[c].color # Faded
         /\ meetingPlace' = c
    /\ UNCHANGED <<state, totalMeetings>>

FadeOut ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings >= M
    /\ \E c \in Creatures :
         /\ state[c].color # Faded
         /\ state' = [state EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<meetingPlace, totalMeetings>>

MeetAndMutate ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ \E c2 \in Creatures :
         /\ c2 # meetingPlace
         /\ LET c1 == meetingPlace IN
              /\ state' = [state EXCEPT ![c1] = [color |-> Complement(state[c1].color, state[c2].color), met |-> state[c1].met + 1],
                                      ![c2] = [color |-> Complement(state[c1].color, state[c2].color), met |-> state[c2].met + 1]]
         /\ totalMeetings' = totalMeetings + 1
    /\ meetingPlace' = MeetingPlaceEmpty

Next ==
    \/ EnterMall
    \/ FadeOut
    \/ MeetAndMutate

Spec == Init /\ [][Next]_<<state, meetingPlace, totalMeetings>>

SumMet == SumOver([c \in Creatures |-> state[c].met], Creatures)

MeetingCountBound == totalMeetings <= M

SumMetMatchesMeetingCount == totalMeetings = M => SumMet = 2 * M

====