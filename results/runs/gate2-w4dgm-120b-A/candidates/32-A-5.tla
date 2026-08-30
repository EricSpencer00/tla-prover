---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME /\ N \in Nat /\ N >= 2
       /\ M \in Nat /\ M >= 1

Creatures == 0 .. (N - 1)
Colors == {"blue", "red", "yellow", Faded}

\* The complement rule: two distinct colors map to the third one, identical
\* colors stay unchanged.
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE LET x \in Colors : x \notin {c1, c2} IN x

RECURSIVE SumCounts(_)
SumCounts(S) ==
    IF S = {} THEN 0
    ELSE LET c == CHOOSE x \in S : TRUE IN c.meetings + SumCounts(S \ {c})

VARIABLES state, mall, total_meetings

vars == <<state, mall, total_meetings>>

TypeOK ==
    /\ state \in [Creatures -> [color : Colors, meetings : 0 .. M]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ total_meetings \in 0 .. M

Init ==
    /\ state \in [Creatures -> [color : {"blue", "red", "yellow"}, meetings : 0]]
    /\ mall = MeetingPlaceEmpty
    /\ total_meetings = 0

EnterMall(c) ==
    /\ state[c].color # Faded
    /\ mall = MeetingPlaceEmpty
    /\ total_meetings < M
    /\ mall' = c
    /\ UNCHANGED <<state, total_meetings>>

FadeOut(c) ==
    /\ state[c].color # Faded
    /\ mall = MeetingPlaceEmpty
    /\ total_meetings >= M
    /\ state' = [state EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<mall, total_meetings>>

\* The arriving creature and the waiting one both adopt the pair-dependent color.
Mutate(c) ==
    /\ mall \in Creatures
    /\ mall # c
    /\ state[c].color # Faded
    /\ total_meetings < M
    /\ LET nc == Complement(state[mall].color, state[c].color) IN
         /\ state' = [state EXCEPT ![mall].color = nc, ![c].color = nc]
    /\ state' = [state EXCEPT ![mall].meetings = @ + 1, ![c].meetings = @ + 1]
    /\ total_meetings' = total_meetings + 1
    /\ mall' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : EnterMall(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : Mutate(c)

Spec == Init /\ [][Next]_vars

\* Each meeting touches two participants, so twice the number of meetings must
\* account for every individual creature's meeting count once the mall has closed.
SumMet ==
    total_meetings = M => SumCounts(Creatures) = 2 * M

====