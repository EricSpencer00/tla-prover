---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Color complement: if the two colors are equal the pair keeps it; otherwise
\* both take the unique third color of the palette {blue, red, yellow}.
Complement(x, y) ==
    IF x = y THEN x
    ELSE CHOOSE z \in { "blue", "red", "yellow" } :
              z # x /\ z # y

VARIABLES state, meetingPlace, totalMeetings

vars == << state, meetingPlace, totalMeetings >>

Creature == 1..N
Color == { "blue", "red", "yellow", Faded }
Entry == Creature \cup { MeetingPlaceEmpty }

RECURSIVE SumOf(_)
SumOf(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN LET rest == SumOf(S \ {x})
            IN LET ct == state[x][2] IN rest + ct

TypeOK ==
    /\ state \in [Creature -> (Color \X Nat)]
    /\ meetingPlace \in Entry
    /\ totalMeetings \in Nat

Init ==
    /\ state \in [Creature -> (Color \X Nat)]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0

\* A non-faded creature enters the meeting place when it is empty and meetings
\* are still permitted.
EnterEmpty(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ state[c][1] # Faded
    /\ totalMeetings < M
    /\ meetingPlace' = c
    /\ UNCHANGED << state, totalMeetings >>

\* After the meeting budget is exhausted an incoming creature fades out instead
\* of entering the meeting place.
FadeOut(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = M
    /\ state[c][1] # Faded
    /\ state' = [state EXCEPT ![c] = << Faded, state[c][2] >>]
    /\ UNCHANGED << meetingPlace, totalMeetings >>

\* Two distinct creatures meet and both adopt the complement of their colors.
MeetAndMutate(c) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ meetingPlace # c
    /\ totalMeetings < M
    /\ LET newc == Complement(state[meetingPlace][1], state[c][1])
       IN state' = [state EXCEPT
                     ![meetingPlace] = << newc, state[meetingPlace][2] + 1 >>,
                     ![c] = << newc, state[c][2] + 1 >>]
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ totalMeetings' = totalMeetings + 1

Next ==
    \/ \E c \in Creature : EnterEmpty(c)
    \/ \E c \in Creature : FadeOut(c)
    \/ \E c \in Creature : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

\* Conservation law: each meeting advances two participants' counts, so at the
\* budget ceiling the summed count equals twice the number of meetings.
SumMet == totalMeetings = M => SumOf(Creature) = 2 * M

====