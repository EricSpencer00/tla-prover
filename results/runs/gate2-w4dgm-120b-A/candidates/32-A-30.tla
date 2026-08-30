---- MODULE Chameneos ----
EXTENDS Integers, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1 .. N
Colors == {"blue", "red", "yellow", Faded}

VARIABLES state, mall, total

vars == <<state, mall, total>>

Sum(f, S) == IF S = {} THEN 0
             ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + Sum(f, S \ {x})

Complement(a, b) ==
    IF a = b THEN a
    ELSE LET others == Colors \ {"faded", a, b} IN CHOOSE o \in others : TRUE

Init ==
    /\ \E c \in [Creatures -> {"blue", "red", "yellow"}] :
           state = [p \in Creatures |-> <<c[p], 0>>]
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

Enter(p) ==
    /\ mall = MeetingPlaceEmpty
    /\ state[p][1] # Faded
    /\ total < M
    /\ mall' = p
    /\ UNCHANGED <<state, total>>

FadeOut(p) ==
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ state[p][1] # Faded
    /\ state' = [state EXCEPT ![p] = <<Faded, state[p][2>>]
    /\ UNCHANGED <<mall, total>>

Meet(q) ==
    /\ mall # MeetingPlaceEmpty
    /\ mall # q
    /\ total < M
    /\ LET na == Complement(state[mall][1], state[q][1]) IN
         state' = [state EXCEPT ![mall] = <<na, state[mall][2] + 1>>,
                               ![q] = <<na, state[q][2] + 1>>]
    /\ mall' = MeetingPlaceEmpty
    /\ total' = total + 1

Next ==
    \/ \E p \in Creatures : Enter(p)
    \/ \E p \in Creatures : FadeOut(p)
    \/ \E q \in Creatures : Meet(q)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ state \in [Creatures -> [color : Colors, met : 0 .. M]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ total \in 0 .. M

SumMet ==
    total = M => Sum([p \in Creatures |-> state[p][2]], Creatures) = 2 * M

====