---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

VARIABLES color, count, meetingPlace, totalMet

vars == <<color, count, meetingPlace, totalMet>>

RECURSIVE SumCounts(_)
SumCounts(S) ==
    IF S = {} THEN 0
    ELSE LET c == CHOOSE e \in S : TRUE
         IN count[c] + SumCounts(S \ {c})

TypeOK ==
    /\ color \in [Creatures -> Colors]
    /\ count \in [Creatures -> Nat]
    /\ meetingPlace \in (Creatures \cup {MeetingPlaceEmpty})
    /\ totalMet \in Nat

Init ==
    /\ \E f \in [Creatures -> {"blue", "red", "yellow"}] :
        color = f
    /\ count = [c \in Creatures |-> 0]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet = 0

Complement(x, y) ==
    IF x = y THEN x
    ELSE LET zs == {"blue", "red", "yellow"} \ {x, y}
         IN CHOOSE z \in zs : TRUE

Enter(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet < M
    /\ color[c] # Faded
    /\ meetingPlace' = c
    /\ UNCHANGED <<color, count, totalMet>>

FadeOut(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet >= M
    /\ color[c] # Faded
    /\ color' = [color EXCEPT ![c] = Faded]
    /\ UNCHANGED <<count, meetingPlace, totalMet>>

Meet(p, c) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ p # c
    /\ color[p] # Faded
    /\ color[c] # Faded
    /\ count' = [count EXCEPT ![p] = count[p] + 1, ![c] = count[c] + 1]
    /\ color' = [color EXCEPT ![p] = Complement(color[p], color[c]), ![c] = Complement(color[p], color[c])]
    /\ totalMet' = totalMet + 1
    /\ meetingPlace' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : Enter(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E p, c \in Creatures : Meet(p, c)

Spec == Init /\ [][Next]_vars

SumMet ==
    (totalMet = M) => (SumCounts(Creatures) = 2 * M)

====