---- MODULE Chameneos ----
EXTENDS Naturals, Sequences

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1..N

Colors == {"blue", "red", "yellow", Faded}

\* The complement rule: if two colors clash, both adopt the third, unrepresented color.
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c \in {"blue", "red", "yellow"} :
            (c # c1) /\ (c # c2)

VARIABLES col, placeOccupant, totalMet

vars == <<col, placeOccupant, totalMet>>

TypeOK ==
    /\ col \in [Creatures -> [col: Colors, met: 0..M]]
    /\ placeOccupant \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0..M

SumMet ==
    LET f[i \in 0..N] ==
        IF i = 0 THEN 0
        ELSE f[i-1] + col[i].met
    IN f[N]

Init ==
    /\ col \in [Creatures -> [col: {"blue", "red", "yellow"}, met: 0]]
    /\ placeOccupant = MeetingPlaceEmpty
    /\ totalMet = 0

\* A creature enters the meeting place to wait for a partner.
Enter(c) ==
    /\ placeOccupant = MeetingPlaceEmpty
    /\ col[c].col # Faded
    /\ totalMet < M
    /\ placeOccupant' = c
    /\ UNCHANGED <<col, totalMet>>

\* With the meeting place closed, a creature that tries to enter fades out.
FadeOut(c) ==
    /\ placeOccupant = MeetingPlaceEmpty
    /\ col[c].col # Faded
    /\ totalMet >= M
    /\ col' = [col EXCEPT ![c].col = Faded]
    /\ UNCHANGED <<placeOccupant, totalMet>>

\* Two creatures meet and both adopt the complement color; the meeting ends.
Meet(c) ==
    /\ placeOccupant # MeetingPlaceEmpty
    /\ placeOccupant # c
    /\ col[c].col # Faded
    /\ col[placeOccupant].col # Faded
    /\ totalMet < M
    /\ col' = [col EXCEPT ![c] = [col |-> Complement(col[c].col, col[placeOccupant].col), met |-> col[c].met + 1],
                              ![placeOccupant] = [col |-> Complement(col[c].col, col[placeOccupant].col), met |-> col[placeOccupant].met + 1]]
    /\ totalMet' = totalMet + 1
    /\ placeOccupant' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : Enter(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

\* Bounded capacity: when the meeting budget is spent, the count of
\* individual meetings equals exactly twice the number of meetings.
\* Every meeting involves exactly two participants.
MeetingBudgetCoherence == (totalMet = M) => (SumMet = 2 * M)

====