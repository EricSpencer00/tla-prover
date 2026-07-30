---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures are identified by the numbers 1..N. Their shared color is one of
\* blue, red, yellow, or the distinguished Faded state.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

\* The meeting place holds at most one waiting creature. A global counter
\* tallies completed meetings; each creature also tracks its own participation.
VARIABLES colorAndCount, waiting, totalMeetings

vars == <<colorAndCount, waiting, totalMeetings>>

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

TotalIndividual == SumOver([c \in Creatures |-> colorAndCount[c][2]], Creatures)

TypeOK ==
  /\ colorAndCount \in [Creatures -> [1..2 -> (Colors \cup {0})]]
  /\ waiting \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ colorAndCount \in [Creatures -> [1..2 -> Colors]]
  /\ \A c \in Creatures :
       /\ colorAndCount[c][1] \in {"blue", "red", "yellow"}
       /\ colorAndCount[c][2] = 0
  /\ waiting = MeetingPlaceEmpty
  /\ totalMeetings = 0

Enter(c) ==
  /\ waiting = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ colorAndCount[c][1] # Faded
  /\ waiting' = c
  /\ UNCHANGED <<colorAndCount, totalMeetings>>

FadeOut(c) ==
  /\ waiting = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ colorAndCount[c][1] # Faded
  /\ colorAndCount' = [colorAndCount EXCEPT ![c][1] = Faded]
  /\ UNCHANGED <<waiting, totalMeetings>>

\* Complementation: equal colors stay, different colors move to the third.
Complement(col1, col2) ==
  IF col1 = col2 THEN col1
  ELSE LET s == {col1, col2} IN CHOOSE z \in {"blue", "red", "yellow"} : z \notin s

MeetAndMutate(c) ==
  /\ waiting # MeetingPlaceEmpty
  /\ waiting # c
  /\ LET col1 == colorAndCount[waiting][1] IN
       LET col2 == colorAndCount[c][1] IN
         /\ ~ (col1 = Faded \/ col2 = Faded)
         /\ LET newcol == Complement(col1, col2) IN
              colorAndCount' = [colorAndCount EXCEPT
                                 ![waiting][1] = newcol,
                                 ![waiting][2] = @ + 1,
                                 ![c][1] = newcol,
                                 ![c][2] = @ + 1]
  /\ waiting' = MeetingPlaceEmpty
  /\ totalMeetings' = totalMeetings + 1

Next ==
  \/ \E c \in Creatures : Enter(c)
  \/ \E c \in Creatures : FadeOut(c)
  \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet == (totalMeetings = M) => (TotalIndividual = 2 * M)

====