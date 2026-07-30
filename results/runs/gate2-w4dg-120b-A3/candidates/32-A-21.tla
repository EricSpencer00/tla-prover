---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS
  N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ M \in Nat /\ N > 0 /\ M > 0

Creatures == 1 .. N

Colors == {"blue", "red", "yellow", Faded}

VARIABLES
  colorOf, meetingsOf, occupant, totalMeetings

vars == << colorOf, meetingsOf, occupant, totalMeetings >>

TypeOK ==
  /\ colorOf \in [Creatures -> Colors]
  /\ meetingsOf \in [Creatures -> Nat]
  /\ occupant \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in Nat

\* A meeting involves two creatures, so the per-creature meeting counts
\* summed together must always be twice the number of meetings completed.
SumMet ==
  /\ totalMeetings = M => totalMeetings + totalMeetings = Sum({meetingsOf[c] : c \in Creatures})
  /\ totalMeetings <= M

Init ==
  /\ colorOf \in [Creatures -> Colors \ {"faded"}]
  /\ meetingsOf = [c \in Creatures |-> 0]
  /\ occupant = MeetingPlaceEmpty
  /\ totalMeetings = 0

Complement(a, b) ==
  IF a = b THEN a ELSE ({ "blue", "red", "yellow" } \ {a, b})[1]

Enter ==
  /\ occupant = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ \E c \in Creatures :
       /\ colorOf[c] # Faded
       /\ occupant' = c
  /\ UNCHANGED << colorOf, meetingsOf, totalMeetings >>

FadeOut ==
  /\ occupant = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ \E c \in Creatures :
       /\ colorOf[c] # Faded
       /\ colorOf' = [colorOf EXCEPT ![c] = Faded]
  /\ UNCHANGED << meetingsOf, occupant, totalMeetings >>

Meet ==
  /\ occupant # MeetingPlaceEmpty
  /\ \E c \in Creatures :
       /\ c # occupant
       /\ colorOf[c] # Faded
       /\ LET newc == Complement(colorOf[occupant], colorOf[c]) IN
            /\ colorOf' = [colorOf EXCEPT ![c] = newc, ![occupant] = newc]
            /\ meetingsOf' = [meetingsOf EXCEPT ![c] = @ + 1, ![occupant] = @ + 1]
       /\ occupant' = MeetingPlaceEmpty
       /\ totalMeetings' = totalMeetings + 1

Next == Enter \/ FadeOut \/ Meet

Spec == Init /\ [][Next]_vars

====