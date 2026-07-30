---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

CREATURES == 1..N
COLORS == {"blue", "red", "yellow", Faded}
CENTER == "center"

VARIABLES state, meetingPlace, totalCount
vars == <<state, meetingPlace, totalCount>>

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

SumCounts == SumOver([c \in CREATURES |-> state[c][2]], CREATURES)

MUTATE(x, y) ==
    IF x = y THEN x
    ELSE IF {x, y} = {"blue", "red"} THEN "yellow"
    ELSE IF {x, y} = {"red", "yellow"} THEN "blue"
    ELSE "red"

InitState ==
    [c \in COLORS |-> CHOOSE n \in CREATURES : TRUE, 0]

Init ==
    /\ state = [c \in CREATURES |-> InitState]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalCount = 0

Enter ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalCount < M
    /\ \E c \in CREATURES :
         /\ state[c][1] # Faded
         /\ meetingPlace' = c
    /\ UNCHANGED <<state, totalCount>>

Fade ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalCount >= M
    /\ \E c \in CREATURES :
         /\ state[c][1] # Faded
         /\ state' = [state EXCEPT ![c][1] = Faded]
    /\ UNCHANGED <<meetingPlace, totalCount>>

Meet ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ \E c \in CREATURES :
         /\ c # meetingPlace
         /\ state[c][1] # Faded
         /\ LET np == MUTATE(state[c][1], state[meetingPlace][1]) IN
              state' = [state EXCEPT ![c] = <<np, @ [2] + 1>>,
                                 ![meetingPlace] = <<np, @ [2] + 1>>]
         /\ totalCount' = totalCount + 1
         /\ meetingPlace' = MeetingPlaceEmpty

Next ==
    \/ Enter
    \/ Fade
    \/ Meet

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ state \in [CREATURES -> COLORS \X (0..M)]
    /\ meetingPlace \in CREATURES \cup {MeetingPlaceEmpty}
    /\ totalCount \in 0..M

SumMet ==
    totalCount = M => SumCounts = 2 * M
====