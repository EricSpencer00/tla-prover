---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* The complement rule: a meeting is an involution on the color pair, and it
\* must be total on the set of colors so that a meeting is always possible.
Colors == { "blue", "red", "yellow", Faded }

\* Given the colors of the two participants, the rule chooses a new color
\* for both of them together.  It is the involution described in the spec.
Complement(x, y) ==
  IF x = y THEN x
  ELSE IF x = "blue" /\ y = "red" \/ x = "red" /\ y = "blue" THEN "yellow"
  ELSE IF x = "blue" /\ y = "yellow" \/ x = "yellow" /\ y = "blue" THEN "red"
  ELSE IF x = "red" /\ y = "yellow" \/ x = "yellow" /\ y = "red" THEN "blue"
  ELSE x

VARIABLES attr, meetingPlace, totalMet

vars == <<attr, meetingPlace, totalMet>>

Init == /\ attr = [c \in 1..N |-> [color |-> CHOOSE k \in Colors \ {Faded} : TRUE, met |-> 0]]
        /\ meetingPlace = MeetingPlaceEmpty
        /\ totalMet = 0

Enter == /\ meetingPlace = MeetingPlaceEmpty
         /\ totalMet < M
         /\ \E c \in 1..N :
              /\ attr[c].color # Faded
              /\ meetingPlace' = c
         /\ UNCHANGED <<attr, totalMet>>

Fade == /\ meetingPlace = MeetingPlaceEmpty
        /\ totalMet >= M
        /\ \E c \in 1..N :
             /\ attr[c].color # Faded
             /\ attr' = [attr EXCEPT ![c].color = Faded]
        /\ UNCHANGED <<meetingPlace, totalMet>>

Meet == /\ meetingPlace # MeetingPlaceEmpty
        /\ \E c \in 1..N :
             /\ c # meetingPlace
             /\ attr[meetingPlace].color # Faded
             /\ attr[c].color # Faded
             /\ LET newc == Complement(attr[meetingPlace].color, attr[c].color) IN
                  attr' = [attr EXCEPT ![c] = [color |-> newc, met |-> @.met + 1],
                                      ![meetingPlace] = [color |-> newc, met |-> @.met + 1]]
             /\ meetingPlace' = MeetingPlaceEmpty
        /\ totalMet' = totalMet + 1

Next == Enter \/ Fade \/ Meet

Spec == Init /\ [][Next]_vars

TypeOK == /\ attr \in [1..N -> [color : Colors, met : 0..M]]
          /\ meetingPlace \in (1..N) \cup {MeetingPlaceEmpty}
          /\ totalMet \in 0..M

SumMet == totalMet = M => (LET sum[c \in 1..N] == IF c = 1 THEN attr[c].met
                                                   ELSE attr[c].met + sum[c - 1]
                            IN sum[N] = 2 * M)

====