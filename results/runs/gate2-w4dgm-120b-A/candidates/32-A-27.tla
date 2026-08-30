---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures are identified by numbers 1..N. The shared meeting place holds at
\* most one waiting creature. Two creatures that meet both adopt their new
\* color via the complement rule and each count one more meeting participated.

ASSUME /\ N \in Nat /\ N >= 1
       /\ M \in Nat /\ M >= 1
       /\ Faded \notin {"blue", "red", "yellow"}

Colors == {"blue", "red", "yellow"}

\* The complement rule: given two creature colors, return the pair of updated
\* colors each will take after meeting.
Complement(x, y) ==
    IF x = y THEN <<x, y>>
    ELSE LET z == CHOOSE c \in Colors : c # x /\ c # y IN <<z, z>>

\* The total number of individual creature-meeting participations, summed over
\* everybody. If every meeting were recorded exactly twice this would equal 2M
\* once the global meeting budget is spent.
RECURSIVE SumF(_, _)
SumF(f, i) == IF i = 0 THEN 0 ELSE f[i] + SumF(f, i - 1)

VARIABLES color, met, waiting, totalMeetings

vars == <<color, met, waiting, totalMeetings>>

TypeOK ==
    /\ color \in [1..N -> Colors \cup {Faded}]
    /\ met \in [1..N -> 0..M]
    /\ waiting \in (1..N) \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0..M

Init ==
    /\ \E c \in [1..N -> Colors] : color = c
    /\ met = [i \in 1..N |-> 0]
    /\ waiting = MeetingPlaceEmpty
    /\ totalMeetings = 0

Enter(i) ==
    /\ waiting = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ color[i] # Faded
    /\ waiting' = i
    /\ UNCHANGED <<color, met, totalMeetings>>

Fade(i) ==
    /\ waiting = MeetingPlaceEmpty
    /\ totalMeetings = M
    /\ color[i] # Faded
    /\ color' = [color EXCEPT ![i] = Faded]
    /\ UNCHANGED <<met, waiting, totalMeetings>>

\* The arriving creature and the waiting creature must be distinct, so a
\* creature never meets itself.
Meet(i) ==
    /\ waiting # MeetingPlaceEmpty
    /\ i # waiting
    /\ LET newColors == Complement(color[i], color[waiting]) IN
        /\ color' = [color EXCEPT ![i] = newColors[1], ![waiting] = newColors[2]]
    /\ met' = [met EXCEPT ![i] = @ + 1, ![waiting] = @ + 1]
    /\ totalMeetings' = totalMeetings + 1
    /\ waiting' = MeetingPlaceEmpty

Next ==
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Fade(i)
    \/ \E i \in 1..N : Meet(i)

Spec == Init /\ [][Next]_vars

\* When the meeting budget is spent, the exhaustive accounting holds exactly:
\* every meeting was recorded twice, once for each participant.
SumMet == totalMeetings = M => SumF(met, N) = 2 * M

====