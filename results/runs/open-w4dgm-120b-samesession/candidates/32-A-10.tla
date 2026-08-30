---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures are identified by 1..N. Color is either an actual hue or Faded;
\* a faded creature has stopped participating but keeps its own meeting count.
\* The meeting place holds at most one waiting creature (or is empty).
VARIABLES color, meetCount, place, totalMet

vars == <<color, meetCount, place, totalMet>>

Creatures == 1..N

\* Sum of individual meeting counts; in a consistent run this equals
\* twice the global count, since every meeting has exactly two participants.
RECURSIVE SumOver(_)
SumOver(S) ==
    IF S = {} THEN 0
    ELSE LET c == CHOOSE x \in S : TRUE IN meetCount[c] + SumOver(S \ {c})

TypeOK ==
    /\ color \in [Creatures -> {Faded} \cup {"blue", "red", "yellow"}]
    /\ meetCount \in [Creatures -> 0..(2 * M)]
    /\ place \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0..M

Init ==
    /\ color \in [Creatures -> {"blue", "red", "yellow"}]
    /\ meetCount = [c \in Creatures |-> 0]
    /\ place = MeetingPlaceEmpty
    /\ totalMet = 0

\* A creature arrives when the place is empty and the meeting limit has not been reached.
Enter(c) ==
    /\ place = MeetingPlaceEmpty
    /\ totalMet < M
    /\ color[c] # Faded
    /\ place' = c
    /\ UNCHANGED <<color, meetCount, totalMet>>

Fade(c) ==
    /\ place = MeetingPlaceEmpty
    /\ totalMet >= M
    /\ color[c] # Faded
    /\ color' = [color EXCEPT ![c] = Faded]
    /\ UNCHANGED <<meetCount, place, totalMet>>

\* The arriving creature (c) meets the waiting one (place), and both adopt the
\* complement of their pair of colors. Neither c nor place may be faded.
Meet(c) ==
    /\ place # MeetingPlaceEmpty
    /\ place # c
    /\ color[c] # Faded
    /\ color[place] # Faded
    /\ totalMet < M
    /\ LET complement(a, b) ==
           IF a = b THEN a
           ELSE {"blue", "red", "yellow"} \ {a, b}
       IN
        /\ color' = [color EXCEPT ![c] = complement(color[c], color[place]),
                               ![place] = complement(color[c], color[place])]
    /\ meetCount' = [meetCount EXCEPT ![c] = @ + 1, ![place] = @ + 1]
    /\ totalMet' = totalMet + 1
    /\ place' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : Enter(c)
    \/ \E c \in Creatures : Fade(c)
    \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

\* At the meeting limit the global counter must reconcile with the individuals.
SumMet == totalMet = M => SumOver(Creatures) = 2 * M

\* The global total is never allowed to exceed the configured meeting limit.
Bounded == totalMet <= M
====