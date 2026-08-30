---- MODULE Chameneos ----
EXTENDS Integers

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 0 .. (N - 1)
Colors == {"blue", "red", "yellow", Faded}

\* The complement rule: given two colors, the result of a meeting between them.
Complement(a, b) ==
    IF a = b THEN a
    ELSE LET theOne == CHOOSE c \in {"blue", "red", "yellow"} : c # a /\ c # b
         IN theOne

VARIABLES state, occupant, meetingsMade

vars == <<state, occupant, meetingsMade>>

TypeOK ==
    /\ state \in [Creatures -> [c : Colors, met : 0 .. M]]
    /\ occupant \in (Creatures \cup {MeetingPlaceEmpty})
    /\ meetingsMade \in 0 .. M

SumOf(f, S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE
                    IN f[x] + SumOf(f, S \ {x})

\* Each meeting involves two participants, so the sum of individual counts is
\* twice the number of meetings; the bound M keeps every count finite.
SumMet == SumOf([c \in Creatures |-> state[c].met], Creatures) = 2 * meetingsMade

\* The non-deterministic initial coloring is what keeps symmetry reduction from
\* collapsing every start state into one.
Init ==
    /\ state \in [Creatures -> [c : {"blue", "red", "yellow"}, met : 0 .. M]]
    /\ occupant = MeetingPlaceEmpty
    /\ meetingsMade = 0

EnterEmpty(c) ==
    /\ occupant = MeetingPlaceEmpty
    /\ meetingsMade < M
    /\ state[c].c # Faded
    /\ occupant' = c
    /\ UNCHANGED <<state, meetingsMade>>

FadeOut(c) ==
    /\ occupant = MeetingPlaceEmpty
    /\ meetingsMade = M
    /\ state[c].c # Faded
    /\ state' = [state EXCEPT ![c].c = Faded]
    /\ UNCHANGED <<occupant, meetingsMade>>

\* Meeting: both participants adopt the rule's result, both counts advance.
Meet(c) ==
    /\ occupant # MeetingPlaceEmpty
    /\ occupant # c
    /\ state[c].c # Faded
    /\ state[occupant].c # Faded
    /\ state' = [state EXCEPT
                    ![c].c = Complement(state[c].c, state[occupant].c),
                    ![occupant].c = Complement(state[c].c, state[occupant].c),
                    ![c].met = @ + 1,
                    ![occupant].met = @ + 1]
    /\ occupant' = MeetingPlaceEmpty
    /\ meetingsMade' = meetingsMade + 1

Next ==
    \/ \E c \in Creatures : EnterEmpty(c) \/ FadeOut(c) \/ Meet(c)

Spec == Init /\ [][Next]_vars

====