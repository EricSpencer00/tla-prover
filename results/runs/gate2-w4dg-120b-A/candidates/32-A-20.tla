---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A creature is a natural-number identifier. Its state is its color together
\* with the number of meetings it has participated in.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
NoSuch == 0

VARIABLES creatureState, place, meetings

vars == <<creatureState, place, meetings>>

\* Sum of all individual meeting counts; used in the safety property.
RECURSIVE SumOver(_)
SumOver(S) ==
  IF S = {} THEN 0
  ELSE LET c == CHOOSE x \in S : TRUE IN creatureState[c][2] + SumOver(S \ {c})

TypeOK ==
  /\ creatureState \in [Creatures -> [Colors \X 0..M]]
  /\ place \in Creatures \cup {MeetingPlaceEmpty}
  /\ meetings \in 0..M

Init ==
  /\ creatureState \in [Creatures -> [Colors \X {0}]]
  /\ place = MeetingPlaceEmpty
  /\ meetings = 0

\* The third (complementary) color given two different ones.
Complement(a, b) ==
  IF a = b THEN a
  ELSE (({"blue", "red", "yellow"} \ {a, b}) \cup {Faded}) \ {Faded}

Enter(c) ==
  /\ place = MeetingPlaceEmpty
  /\ meetings < M
  /\ creatureState[c][1] # Faded
  /\ place' = c
  /\ UNCHANGED <<creatureState, meetings>>

Fade(c) ==
  /\ place = MeetingPlaceEmpty
  /\ meetings = M
  /\ creatureState[c][1] # Faded
  /\ creatureState' = [creatureState EXCEPT ![c] = <<Faded, creatureState[c][2>>]]
  /\ UNCHANGED <<place, meetings>>

\* Two creatures never meet themselves; both participants change color.
Meet(c) ==
  /\ place # MeetingPlaceEmpty
  /\ place # c
  /\ meetings < M
  /\ LET col1 == creatureState[c][1]
         col2 == creatureState[place][1]
         newcol == Complement(col1, col2)
      IN
        /\ creatureState' = [creatureState EXCEPT
                               ![c] = <<newcol, creatureState[c][2] + 1>>,
                               ![place] = <<newcol, creatureState[place][2] + 1>>]
        /\ meetings' = meetings + 1
        /\ place' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : Enter(c)
  \/ \E c \in Creatures : Fade(c)
  \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

\* Bounded convergence: once the meeting limit is reached, every individual
\* count must add up to exactly twice the number of meetings.
SumMet == meetings = M => SumOver(Creatures) = 2 * M

====