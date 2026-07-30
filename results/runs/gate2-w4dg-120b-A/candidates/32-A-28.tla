---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N > 0
ASSUME M \in Nat /\ M > 0

Creatures == 0 .. N-1

Colors == {"blue", "red", "yellow", Faded}

VARIABLES colorCount, meetingPlace, meetings

vars == <<colorCount, meetingPlace, meetings>>

SumCounts == LET g[S \in SUBSET Creatures] ==
                IF S = {} THEN 0
                ELSE LET c == CHOOSE x \in S : TRUE
                     IN colorCount[c][2] + g[S \ {c}]
             IN g[Creatures]

Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE IF {c1, c2} = {"blue", "red"} THEN "yellow"
    ELSE IF {c1, c2} = {"red", "yellow"} THEN "blue"
    ELSE "red"

TypeOK ==
    /\ colorCount \in [Creatures -> Colors \X (0..M)]
    /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ meetings \in 0..M

Init ==
    /\ \E f \in [Creatures -> Colors]:
        /\ \A c \in Creatures: colorCount[c] = <<f[c], 0>>
    /\ meetingPlace = MeetingPlaceEmpty
    /\ meetings = 0

EnterPlace(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ meetings < M
    /\ colorCount[c][1] # Faded
    /\ meetingPlace' = c
    /\ UNCHANGED <<colorCount, meetings>>

FadeOut(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ meetings = M
    /\ colorCount[c][1] # Faded
    /\ colorCount' = [colorCount EXCEPT ![c] = <<Faded, colorCount[c][2]>>]
    /\ UNCHANGED <<meetingPlace, meetings>>

MeetAndMutate(c) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ meetingPlace # c
    /\ colorCount[meetingPlace][1] # Faded
    /\ LET c1 == colorCount[meetingPlace][1]
           c2 == colorCount[c][1]
           newcol == Complement(c1, c2)
       IN
        /\ colorCount' = [colorCount EXCEPT
                            ![meetingPlace] = <<newcol, colorCount[meetingPlace][2] + 1>>,
                            ![c] = <<newcol, colorCount[c][2] + 1>>]
    /\ meetings' = meetings + 1
    /\ meetingPlace' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures: EnterPlace(c)
    \/ \E c \in Creatures: FadeOut(c)
    \/ \E c \in Creatures: MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet == meetings = M => SumCounts = 2 * M

====