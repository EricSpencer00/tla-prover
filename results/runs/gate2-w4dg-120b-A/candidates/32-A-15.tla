---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N >= 1 /\ M \in Nat /\ M >= 1

Creatures == 0 .. (N - 1)
Colors == {"blue", "red", "yellow", Faded}
InitColors == {"blue", "red", "yellow"}

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN f[x] + SumOf(f, S \ {x})

\* Complement rule: two identical colors stay the same; two different ones
\* both become the third color not present among them.
ColorComplement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE LET others == {"blue", "red", "yellow"} \ {c1, c2}
         IN CHOOSE c \in others : TRUE

VARIABLES col, met, place, totalMet

vars == <<col, met, place, totalMet>>

TypeOK ==
    /\ col \in [Creatures -> Colors]
    /\ met \in [Creatures -> 0..M]
    /\ place \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0..M

Init ==
    /\ col \in [Creatures -> InitColors]
    /\ met = [c \in Creatures |-> 0]
    /\ place = MeetingPlaceEmpty
    /\ totalMet = 0

EnterWaiting(c) ==
    /\ place = MeetingPlaceEmpty
    /\ totalMet < M
    /\ col[c] # Faded
    /\ place' = c
    /\ UNCHANGED <<col, met, totalMet>>

FadeOut(c) ==
    /\ place = MeetingPlaceEmpty
    /\ totalMet = M
    /\ col[c] # Faded
    /\ col' = [col EXCEPT ![c] = Faded]
    /\ UNCHANGED <<met, place, totalMet>>

\* Both participants are re-colored together; the waiting spot is freed.
MeetAndMutate(c) ==
    /\ place # MeetingPlaceEmpty
    /\ place # c
    /\ col[c] # Faded
    /\ col[place] # Faded
    /\ col' = [col EXCEPT ![c] = ColorComplement(col[c], col[place]), ![place] = ColorComplement(col[c], col[place])]
    /\ met' = [met EXCEPT ![c] = met[c] + 1, ![place] = met[place] + 1]
    /\ totalMet' = totalMet + 1
    /\ place' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : EnterWaiting(c) \/ FadeOut(c) \/ MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet == totalMet = (1/2) * SumOf(met, Creatures)

====