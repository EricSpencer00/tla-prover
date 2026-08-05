---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N >= 1 /\ M \in Nat /\ M >= 1

Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
InitColors == {"blue", "red", "yellow"}

VARIABLES color, metCount, waitingInPlace, totalMet
vars == <<color, metCount, waitingInPlace, totalMet>>

\* The complement rule: if two creatures have the same color they keep it,
\* otherwise both adopt the third color the pair does not hold.
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE LET s == {c1, c2} IN CHOOSE c \in InitColors : c \notin s

\* Safe: metCount is a per-creature count, so we sum over all N of them.
SumMet == metCount[1] + metCount[2] + metCount[3] = totalMet
  + metCount[4] + metCount[5] + metCount[6] + metCount[7] + metCount[8] + metCount[9]

TypeOK ==
  /\ metCount \in [Creatures -> 0..M]
  /\ waitingInPlace \in Creatures \cup {MeetingPlaceEmpty}

Init ==
  /\ \E initc \in [Creatures -> InitColors] :
       /\ color = initc
       /\ metCount = [c \in Creatures |-> 0]
  /\ waitingInPlace = MeetingPlaceEmpty
  /\ totalMet = 0

EnterPlace(c) ==
  /\ waitingInPlace = MeetingPlaceEmpty
  /\ totalMet < M
  /\ color[c] # Faded
  /\ waitingInPlace' = c
  /\ UNCHANGED <<color, metCount, totalMet>>

FadeOut(c) ==
  /\ waitingInPlace = MeetingPlaceEmpty
  /\ totalMet >= M
  /\ color[c] # Faded
  /\ color' = [color EXCEPT ![c] = Faded]
  /\ UNCHANGED <<metCount, waitingInPlace, totalMet>>

MeetMutate(c) ==
  /\ waitingInPlace # MeetingPlaceEmpty
  /\ waitingInPlace # c
  /\ totalMet < M
  /\ color[c] # Faded
  /\ color[waitingInPlace] # Faded
  /\ \E newc \in InitColors :
       /\ color' = [color EXCEPT ![c] = newc, ![waitingInPlace] = newc]
  /\ metCount' = [metCount EXCEPT ![c] = metCount[c] + 1, ![waitingInPlace] = metCount[waitingInPlace] + 1]
  /\ totalMet' = totalMet + 1
  /\ waitingInPlace' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : EnterPlace(c) \/ FadeOut(c) \/ MeetMutate(c)

Spec == Init /\ [][Next]_vars

====