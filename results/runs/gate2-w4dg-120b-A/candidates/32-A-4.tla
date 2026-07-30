---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* MeetingPlaceEmpty marks the meeting place when no creature is waiting in it.
\* Faded is the terminal color a creature takes once the meeting place has closed.
\* N is the total number of meetings the place will tolerate; M is the creature count.

\* State: a creature's color and its attended-meeting count, the meeting-place occupant,
\* and the global count of completed meetings.
VARIABLES state, mall, total

vars == << state, mall, total >>

\* The complement rule: a single different color is chosen whenever the two creatures
\* differ, and the same color is kept when they already match.
Complement(c1, c2) ==
  IF c1 = c2
  THEN IF c1 = "blue" THEN "blue" ELSE IF c1 = "red" THEN "red" ELSE "yellow"
  ELSE IF c1 = "blue" /\ c2 = "red" THEN "yellow"
       ELSE IF c1 = "red" /\ c2 = "blue" THEN "yellow"
            ELSE IF c1 = "red" /\ c2 = "yellow" THEN "blue"
                 ELSE IF c1 = "yellow" /\ c2 = "red" THEN "blue"
                      ELSE IF c1 = "blue" /\ c2 = "yellow" THEN "red"
                           ELSE "red"

Creatures == 1..M

Recur(c) == state[c][1]
Met(c)   == state[c][2]

TotalMet ==
  LET add[S \in SUBSET Creatures] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE IN Met(x) + add[S \ {x}]
  IN add[Creatures]

RECURSIVE SumState(_)
SumState(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN Met(x) + SumState(S \ {x})

TypeOK ==
  /\ state \in [Creatures -> {"blue", "red", "yellow", Faded} \X Nat]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in 0..N

Init ==
  /\ \E f \in [Creatures -> {"blue", "red", "yellow"}]:
       state = [c \in Creatures |-> << f[c], 0 >>]
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

\* Enter: a non-faded creature takes the empty meeting place, provided the place
\* is still open.
Enter(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ total < N
  /\ Recur(c) # Faded
  /\ mall' = c
  /\ UNCHANGED << state, total >>

\* Fade out: with the place closed, a non-faded creature whose entry is refused
\* becomes permanently faded.
Fade(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ total >= N
  /\ Recur(c) # Faded
  /\ state' = [state EXCEPT ![c] = << Faded, @ [2] >>]
  /\ UNCHANGED << mall, total >>

\* Meet: the arriving creature and the waiting occupant, being distinct, both take
\* the complement color, record the meeting, and clear the place.
Meet(c) ==
  /\ mall # MeetingPlaceEmpty
  /\ mall # c
  /\ Recur(c) # Faded
  /\ Recur(mall) # Faded
  /\ LET newc == Complement(Recur(c), Recur(mall))
     IN state' = [state EXCEPT ![c] = << newc, @ [2] + 1 >>,
                              ![mall] = << newc, @ [2] + 1 >>]
  /\ total' = total + 1
  /\ mall' = MeetingPlaceEmpty

Next == \E c \in Creatures: Enter(c) \/ Fade(c) \/ Meet(c)

Spec == Init /\ [][Next]_vars

SumMet ==
  (total = N) => (TotalMet = 2 * N)

====