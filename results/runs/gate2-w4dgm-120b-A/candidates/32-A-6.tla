---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Each creature holds a color and its personal meeting count; the meeting place
\* admits at most one waiting creature, and a global counter tracks total meetings.
Creatures == 0..(N - 1)
Colors == {"blue", "red", "yellow", Faded}
Third(c, d) == IF (c = "blue" /\ d = "red") \/ (c = "red" /\ d = "blue") THEN "yellow"
               ELSE IF (c = "red" /\ d = "yellow") \/ (c = "yellow" /\ d = "red") THEN "blue"
               ELSE IF (c = "blue" /\ d = "yellow") \/ (c = "yellow" /\ d = "blue") THEN "red"
               ELSE c

VARIABLES state, mall, totalMet

TypeOK ==
    /\ state \in [Creatures -> [col: Colors, metCount: 0..M]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0..M

Init ==
    /\ state = [c \in Creatures |-> [col |-> "blue", metCount |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ totalMet = 0

\* A creature that cannot enter because the place is closed simply fades out.
EnterPlace(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMet < M
    /\ state[c].col # Faded
    /\ mall' = c
    /\ UNCHANGED <<state, totalMet>>

FadeOut(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ totalMet = M
    /\ state[c].col # Faded
    /\ state' = [state EXCEPT ![c].col = Faded]
    /\ UNCHANGED <<mall, totalMet>>

\* Two distinct creatures meet; their colors change by the complement rule.
Meet(c) ==
    /\ mall \in Creatures
    /\ mall # c
    /\ state[c].col # Faded
    /\ state[mall].col # Faded
    /\ totalMet < M
    /\ LET newc == Third(state[c].col, state[mall].col) IN
        state' = [state EXCEPT ![c] = [col |-> newc, metCount |-> @.metCount + 1],
                             ![mall] = [col |-> newc, metCount |-> @.metCount + 1]]
    /\ mall' = MeetingPlaceEmpty
    /\ totalMet' = totalMet + 1

Next ==
    \/ \E c \in Creatures: EnterPlace(c)
    \/ \E c \in Creatures: FadeOut(c)
    \/ \E c \in Creatures: Meet(c)

Spec == Init /\ [][Next]_<<state, mall, totalMet>>

\* Every meeting involves exactly two participants, so when the meeting budget is
\* spent the summed personal counts must be exactly twice the total meetings.
SumMet ==
    LET sum[T \in SUBSET Creatures] ==
        IF T = {} THEN 0
        ELSE LET x == CHOOSE y \in T : TRUE IN state[x].metCount + sum[T \ {x}]
    IN sum[Creatures] = 2 * totalMet

\* Individual meeting counts stay within the global budget, so every creature
\* eventually stops participating once the budget is spent.
BoundedMet == \A c \in Creatures: state[c].metCount <= totalMet

====