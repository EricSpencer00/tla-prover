---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N > 0 /\ M \in Nat /\ M > 0 /\ Faded \in 0..3 /\ MeetingPlaceEmpty \in 0..N

Creatures == 1..N
Colors == 0..2

RECURSIVE SumOver(_)
SumOver(S) == IF S = {} THEN 0
              ELSE LET x == CHOOSE y \in S : TRUE IN x + SumOver(S \ {x})

\* Each creature is a pair: its current color, and its individual meeting count.
\* The meeting place is either empty or holds exactly one waiting creature.
Vars == [state : [Creatures -> (Colors \cup {Faded}) \X Nat],
         meetingPlace : Creatures \cup {MeetingPlaceEmpty},
         totalMeetings : Nat]

TypeOK ==
    /\ Vars.state \in [Creatures -> (Colors \cup {Faded}) \X Nat]
    /\ Vars.meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ Vars.totalMeetings \in 0..M

\* Each creature starts with a nondeterministic color and zero meetings.
Init ==
    /\ Vars.state \in [Creatures -> (Colors \cup {Faded}) \X Nat]
    /\ \A c \in Creatures : (Vars.state[c])[2] = 0
    /\ Vars.meetingPlace = MeetingPlaceEmpty
    /\ Vars.totalMeetings = 0

\* Complement rule: same color stays the same; different colors adopt the third.
\* Colors are encoded so "1 + x + y" modulo three yields exactly that.
Complement(c, d) ==
    LET a == (Vars.state[c])[1] IN
    LET b == (Vars.state[d])[1] IN
    IF a = b THEN a ELSE (1 + a + b) % 3

Enter(c) ==
    /\ Vars.meetingPlace = MeetingPlaceEmpty
    /\ Vars.totalMeetings < M
    /\ (Vars.state[c])[1] # Faded
    /\ Vars' = [Vars EXCEPT !.meetingPlace = c]
    /\ UNCHANGED <<state, totalMeetings>>

FadeOut(c) ==
    /\ Vars.meetingPlace = MeetingPlaceEmpty
    /\ Vars.totalMeetings = M
    /\ (Vars.state[c])[1] # Faded
    /\ Vars.state' = [Vars.state EXCEPT ![c] = <<Faded, (Vars.state[c])[2]>>]
    /\ UNCHANGED <<meetingPlace, totalMeetings>>

Meet(c) ==
    /\ Vars.meetingPlace # MeetingPlaceEmpty
    /\ Vars.meetingPlace # c
    /\ Vars.totalMeetings < M
    /\ LET col == Complement(c, Vars.meetingPlace) IN
       Vars.state' = [Vars.state EXCEPT ![c] = <<col, (Vars.state[c])[2] + 1>,
                                      ![Vars.meetingPlace] = <<col, (Vars.state[Vars.meetingPlace])[2] + 1>>]
    /\ Vars.meetingPlace' = MeetingPlaceEmpty
    /\ Vars.totalMeetings' = Vars.totalMeetings + 1

Next ==
    \/ \E c \in Creatures : Enter(c) \/ FadeOut(c) \/ Meet(c)

\* A creature may be stuck faded while others are still trying to join.
Spec == Init /\ [][Next]_Vars

\* When the meeting place closes, the two halves of each meeting must balance.
SumMet == Vars.totalMeetings = M => SumOver({(Vars.state[c])[2] : c \in Creatures}) = 2 * M

====