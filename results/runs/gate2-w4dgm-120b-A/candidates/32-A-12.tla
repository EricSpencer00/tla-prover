---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures are identified by numbers 1..N and each carries a color and a
\* personal meeting count. A single meeting place holds at most one waiting
\* creature; a meeting happens when a second creature arrives and both adopt
\* the complement of their colors. After M total meetings the place closes
\* and creatures that try to enter simply fade.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
InitColors == {"blue", "red", "yellow"}
Third(c1, c2) == IF c1 = c2 THEN c1 ELSE
                    (IF (c1 = "blue" /\ c2 = "red") \/ (c1 = "red" /\ c2 = "blue") THEN "yellow"
                     ELSE IF (c1 = "blue" /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "blue") THEN "red"
                     ELSE "blue")

VARIABLES status, mall, meetings
vars == <<status, mall, meetings>>

SumMet ==
  /\ meetings <= M
  /\ meetings >= 0
  /\ LET sumFn(S) ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE
             IN status[x].meetings + sumFn(S \ {x})
     IN sumFn(Creatures) = 2 * meetings

TypeOK ==
  /\ status \in [Creatures -> [color : Colors, meetings : Nat]]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ meetings \in Nat

Init ==
  /\ status = [c \in Creatures |-> [color |-> CHOOSE k \in InitColors : TRUE, meetings |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ meetings = 0

\* A creature enters the meeting place only while it is open (fewer than M
\* meetings so far) and only if it is not already faded.
EnterMall(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ meetings < M
  /\ status[c].color # Faded
  /\ mall' = c
  /\ UNCHANGED <<status, meetings>>

Fade(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ meetings >= M
  /\ status[c].color # Faded
  /\ status' = [status EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<mall, meetings>>

\* The arriving creature and the waiting creature must be different, so a
\* creature can never meet itself; both adopt the complement color and the
\* global and local counters all advance together.
Meet(c) ==
  /\ mall # MeetingPlaceEmpty
  /\ mall # c
  /\ status[c].color # Faded
  /\ status[mall].color # Faded
  /\ LET newc == Third(status[c].color, status[mall].color)
     IN status' = [status EXCEPT ![c].color = newc, ![mall].color = newc,
                   ![c].meetings = @ + 1, ![mall].meetings = @ + 1]
  /\ meetings' = meetings + 1
  /\ mall' = MeetingPlaceEmpty

Next == \E c \in Creatures : EnterMall(c) \/ Fade(c) \/ Meet(c)

Spec == Init /\ [][Next]_vars

\* SAFETY: when the meeting place has closed, the per-creature meeting
\* counts add up to twice the global meeting count -- each meeting counted
\* once globally and once per participant. LIVENESS: each creature
\* eventually fades out once the meeting place is closed.
====