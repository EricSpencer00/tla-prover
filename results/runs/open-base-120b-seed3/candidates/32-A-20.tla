---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Set of creature identifiers
Creatures == 1..N

\* Set of possible colors (including the special faded color)
Colors == {"blue", "red", "yellow", Faded}
BaseColors == {"blue", "red", "yellow"}

\* Complement rule: if the colors are the same, keep that color;
\* otherwise both adopt the third color.
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CASE /\ c1 = "blue"  /\ c2 = "red"
       \/ c1 = "red"   /\ c2 = "blue"  -> "yellow"
     [] /\ c1 = "blue"  /\ c2 = "yellow"
       \/ c1 = "yellow"/\ c2 = "blue"   -> "red"
     [] /\ c1 = "red"   /\ c2 = "yellow"
       \/ c1 = "yellow"/\ c2 = "red"    -> "blue"
     [] OTHER -> Faded \* (should never happen)

VARIABLES cstate, mall, total

\* cstate maps each creature to a record [color, meetings]
\* mall is either MeetingPlaceEmpty or the identifier of a waiting creature
\* total counts the number of completed meetings
vars == <<cstate, mall, total>>

Init ==
  /\ cstate \in [Creatures -> [color : BaseColors, meetings : Nat]]
  /\ \A c \in Creatures: cstate[c].meetings = 0
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

Enter ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ \E c \in Creatures :
        /\ cstate[c].color # Faded
        /\ mall' = c
        /\ UNCHANGED <<cstate, total>>

FadeOut ==
  /\ mall = MeetingPlaceEmpty
  /\ total = M
  /\ \E c \in Creatures :
        /\ cstate[c].color # Faded
        /\ cstate' = [cstate EXCEPT ![c].color = Faded]
        /\ UNCHANGED <<mall, total>>

MeetAndMutate ==
  /\ mall # MeetingPlaceEmpty
  /\ total < M
  /\ \E c \in Creatures :
        /\ c # mall
        /\ cstate[c].color # Faded
        /\ cstate[mall].color # Faded
        /\ LET newcol == Complement(cstate[c].color, cstate[mall].color) IN
           /\ cstate' = [cstate EXCEPT
                ![c].color    = newcol,
                ![c].meetings = @ + 1,
                ![mall].color    = newcol,
                ![mall].meetings = @ + 1]
        /\ total' = total + 1
        /\ mall' = MeetingPlaceEmpty

Next == \/ Enter \/ FadeOut \/ MeetAndMutate

Spec == Init /\ [][Next]_vars

\* Type invariant
TypeOK ==
  /\ cstate \in [Creatures -> [color : Colors, meetings : Nat]]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in Nat
  /\ total <= M

\* Safety invariant: when total = M, the sum of all individual meeting counts = 2*M
SumMet ==
  total = M => (+/ i \in Creatures : cstate[i].meetings) = 2 * M

====