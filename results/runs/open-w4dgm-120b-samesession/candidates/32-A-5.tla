---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creature identifiers are integers 1..N. Colors are the three chameneos
\* colors plus the faded terminal marker.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

VARIABLES color, personal, place, total

vars == <<color, personal, place, total>>

RECURSIVE SumOver(_)
SumOver(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN personal[x] + SumOver(S \ {x})

TypeOK ==
    /\ color \in [Creatures -> Colors]
    /\ personal \in [Creatures -> 0..(2 * M)]
    /\ place \in Creatures \cup {MeetingPlaceEmpty}
    /\ total \in 0..M

Init ==
    /\ \E c \in [Creatures -> {"blue", "red", "yellow"}] : color = c
    /\ personal = [k \in Creatures |-> 0]
    /\ place = MeetingPlaceEmpty
    /\ total = 0

\* The complement rule: two distinct colors yield the third, equal colors stay.
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE LET others == {"blue", "red", "yellow"} \ {c1, c2}
         IN CHOOSE x \in others : TRUE

EnterPlace(k) ==
    /\ place = MeetingPlaceEmpty
    /\ total < M
    /\ color[k] # Faded
    /\ place' = k
    /\ UNCHANGED <<color, personal, total>>

FadeOut(k) ==
    /\ place = MeetingPlaceEmpty
    /\ total = M
    /\ color[k] # Faded
    /\ color' = [color EXCEPT ![k] = Faded]
    /\ UNCHANGED <<personal, place, total>>

\* The meeting place empties atomically as the two creatures finish meeting.
Meet(k) ==
    /\ place # MeetingPlaceEmpty
    /\ k # place
    /\ color[k] # Faded
    /\ total < M
    /\ LET nc == Complement(color[place], color[k]) IN
         /\ color' = [color EXCEPT ![k] = nc, ![place] = nc]
         /\ personal' = [personal EXCEPT ![k] = personal[k] + 1, ![place] = personal[place] + 1]
    /\ total' = total + 1
    /\ place' = MeetingPlaceEmpty

Next == \E k \in Creatures : EnterPlace(k) \/ FadeOut(k) \/ Meet(k)

Spec == Init /\ [][Next]_vars

SumMet == total = M => SumOver(Creatures) = 2 * M
====