---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 0..(N - 1)
Colors == {"blue", "red", "yellow", Faded}

VARIABLES color, meetings, mallOccupant, totalMeetings

vars == <<color, meetings, mallOccupant, totalMeetings>>

Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE LET s == {"blue", "red", "yellow"} \ {c1, c2} IN CHOOSE c \in s : TRUE

SumOf(f) == LET g[S \in SUBSET Creatures] ==
                  IF S = {} THEN 0
                  ELSE LET x == CHOOSE y \in S : TRUE
                       IN f[x] + g[S \ {x}]
            IN g[Creatures]

TypeOK ==
    /\ color \in [Creatures -> Colors]
    /\ meetings \in [Creatures -> 0..M]
    /\ mallOccupant \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0..M

Init ==
    /\ \E assign \in [Creatures -> {"blue", "red", "yellow"}] :
         color = assign
    /\ meetings = [c \in Creatures |-> 0]
    /\ mallOccupant = MeetingPlaceEmpty
    /\ totalMeetings = 0

EnterMall(c) ==
    /\ mallOccupant = MeetingPlaceEmpty
    /\ color[c] # Faded
    /\ totalMeetings < M
    /\ mallOccupant' = c
    /\ UNCHANGED <<color, meetings, totalMeetings>>

FadeOut(c) ==
    /\ mallOccupant = MeetingPlaceEmpty
    /\ color[c] # Faded
    /\ totalMeetings >= M
    /\ color' = [color EXCEPT ![c] = Faded]
    /\ UNCHANGED <<meetings, mallOccupant, totalMeetings>>

MeetAndMutate(c) ==
    /\ mallOccupant # MeetingPlaceEmpty
    /\ mallOccupant # c
    /\ totalMeetings < M
    /\ LET c1 == mallOccupant
           c2 == c
           newcol == Complement(color[c1], color[c2])
       IN /\ color' = [color EXCEPT ![c1] = newcol, ![c2] = newcol]
          /\ meetings' = [meetings EXCEPT ![c1] = @ + 1, ![c2] = @ + 1]
    /\ mallOccupant' = MeetingPlaceEmpty
    /\ totalMeetings' = totalMeetings + 1

Next ==
    \/ \E c \in Creatures : EnterMall(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet ==
    (totalMeetings = M) => (SumOf(meetings) = 2 * M)

====