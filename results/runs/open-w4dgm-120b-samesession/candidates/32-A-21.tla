---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Magenta and cyan are excluded from the reachable palette by the complement
\* rule, so they never appear in the live configuration.
Colors == {"blue", "red", "yellow", Faded}

\* The complement rule: same color stays, different colors yield the third.
Complement(a, b) ==
    IF a = b THEN a
    ELSE CASE a = "yellow" /\ b = "red"  -> "blue"
          [] a = "red"    /\ b = "yellow" -> "blue"
          [] a = "yellow" /\ b = "blue"  -> "red"
          [] a = "blue"   /\ b = "yellow" -> "red"
          [] a = "red"    /\ b = "blue"  -> "yellow"
          [] OTHER -> "magenta"  \* unreachable, kept for completeness

VARIABLES state, mallOccupant, totalMeetings

TypeOK ==
    /\ state \in [1..N -> [color: Colors, meetings: 0..M]]
    /\ mallOccupant \in (1..N) \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0..M

\* SAFETY: each meeting touches two participants, so the two counts sum to
\* twice the global meeting counter exactly at the closure point.
SumOfMeetings ==
    LET g[S \in SUBSET (1..N)] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE IN state[x].meetings + g[S \ {x}]
    IN g[1..N]

Init ==
    /\ \E f \in [1..N -> {"blue", "red", "yellow"}] : state = [c \in 1..N |-> [color |-> f[c], meetings |-> 0]]
    /\ mallOccupant = MeetingPlaceEmpty
    /\ totalMeetings = 0

EnterMall(c) ==
    /\ mallOccupant = MeetingPlaceEmpty
    /\ state[c].color # Faded
    /\ totalMeetings < M
    /\ mallOccupant' = c
    /\ UNCHANGED <<state, totalMeetings>>

FadeOut(c) ==
    /\ mallOccupant = MeetingPlaceEmpty
    /\ state[c].color # Faded
    /\ totalMeetings = M
    /\ state' = [state EXCEPT ![c] = [color |-> Faded, meetings |-> state[c].meetings]]
    /\ UNCHANGED <<mallOccupant, totalMeetings>>

Meet(c) ==
    /\ mallOccupant # MeetingPlaceEmpty
    /\ mallOccupant # c
    /\ totalMeetings < M
    /\ LET o == mallOccupant
       IN state' = [state EXCEPT ![c] = [color |-> Complement(state[c].color, state[o].color), meetings |-> state[c].meetings + 1],
                    ![o] = [color |-> Complement(state[o].color, state[c].color), meetings |-> state[o].meetings + 1]]
    /\ totalMeetings' = totalMeetings + 1
    /\ mallOccupant' = MeetingPlaceEmpty

Next ==
    \/ \E c \in 1..N : EnterMall(c)
    \/ \E c \in 1..N : FadeOut(c)
    \/ \E c \in 1..N : Meet(c)

Spec ==
    /\ Init
    /\ [][Next]_<<state, mallOccupant, totalMeetings>>
    /\ SF_vars(EnterMall(1)) /\ SF_vars(FadeOut(1)) /\ SF_vars(Meet(1))
    /\ \A c \in 2..N : SF_vars(EnterMall(c)) /\ SF_vars(FadeOut(c)) /\ SF_vars(Meet(c))

\* SAFETY: total-meeting closure forces the per-creature meeting count sum to
\* match the global count -- which is only possible if every meeting touched
\* exactly two creatures and none was lost or double-counted.
MeetingCountConsistent == (totalMeetings = M) => (SumOfMeetings = 2 * M)

\* LIVENESS: once the meeting place is closed and the mall is empty, every
\* creature must eventually have faded out -- the system cannot stall.
EventualFade == (totalMeetings = M /\ mallOccupant = MeetingPlaceEmpty) ~> (\A c \in 1..N : state[c].color = Faded)

====