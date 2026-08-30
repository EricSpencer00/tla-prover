---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N >= 2 /\ M \in Nat /\ M >= 1

Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE LET third[x] == IF x = "blue" THEN "red"
                        ELSE IF x = "red" THEN "yellow"
                        ELSE "blue" IN third[c1]

RECURSIVE SumCounts(_)
SumCounts(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN x + SumCounts(S \ {x})

VARIABLES color, place, totalMeetings

vars == <<color, place, totalMeetings>>

TypeOK ==
    /\ color \in [Creatures -> {Colors}]
    /\ place \in (Creatures \cup {MeetingPlaceEmpty})
    /\ totalMeetings \in 0..M

Init ==
    /\ \E initialColors \in [Creatures -> {"blue", "red", "yellow"}] :
        color = initialColors
    /\ place = MeetingPlaceEmpty
    /\ totalMeetings = 0

Enter(c) ==
    /\ place = MeetingPlaceEmpty
    /\ color[c] # Faded
    /\ totalMeetings < M
    /\ place' = c
    /\ UNCHANGED <<color, totalMeetings>>

FadeOut(c) ==
    /\ place = MeetingPlaceEmpty
    /\ color[c] # Faded
    /\ totalMeetings >= M
    /\ color' = [color EXCEPT ![c] = Faded]
    /\ UNCHANGED <<place, totalMeetings>>

MeetAndMutate(c) ==
    /\ place # MeetingPlaceEmpty
    /\ place # c
    /\ color[c] # Faded
    /\ color' = [color EXCEPT ![c] = Complement(color[c], color[place]),
                                ![place] = Complement(color[c], color[place])]
    /\ totalMeetings' = totalMeetings + 1
    /\ place' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : Enter(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

EveryMeetingCountsTwice ==
    totalMeetings = M => SumCounts(\{color[c] : c \in Creatures\}) = 2 * M

====