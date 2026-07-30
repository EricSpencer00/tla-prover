---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

\* Creatures (called chameneos) pair up at a single shared meeting place.  When
\* two different creatures meet they both change color according to a
\* complementation rule.  After a fixed total number of meetings the place
\* closes and creatures trying to enter fade out.  The invariant protects
\* the accounting of meetings: once the global counter is at capacity the sum
\* of each creature's personal meeting count must be exactly twice that
\* capacity, because every meeting counts for both participants.

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1..N
Colors == {"blue", "red", "yellow"}
Complement(c1, c2) == IF c1 = c2 THEN c1 ELSE CHOOSE c \in Colors : c # c1 /\ c # c2

VARIABLES colorAndCount, place, grandTotal

vars == <<colorAndCount, place, grandTotal>>

RECURSIVE SumCount(_)
SumCount(S) == IF S = {} THEN 0 ELSE
                 LET c == CHOOSE x \in S : TRUE IN colorAndCount[c][2] + SumCount(S \ {c})

TypeOK ==
  /\ colorAndCount \in [Creatures -> (Colors \cup {Faded}) \X (0..M)]
  /\ place \in Creatures \cup {MeetingPlaceEmpty}
  /\ grandTotal \in 0..M

Init ==
  /\ \E f \in [Creatures -> Colors \X {0}]:
        /\ (\A c \in Creatures : f[c][1] = 0)
        /\ colorAndCount = f
  /\ place = MeetingPlaceEmpty
  /\ grandTotal = 0

EnterPlace ==
  /\ place = MeetingPlaceEmpty
  /\ grandTotal < M
  /\ \E c \in Creatures :
       /\ colorAndCount[c][1] # Faded
       /\ place' = c
  /\ UNCHANGED <<colorAndCount, grandTotal>>

Fade ==
  /\ place = MeetingPlaceEmpty
  /\ grandTotal = M
  /\ \E c \in Creatures :
       /\ colorAndCount[c][1] # Faded
       /\ colorAndCount' = [colorAndCount EXCEPT ![c][1] = Faded]
  /\ UNCHANGED <<place, grandTotal>>

MeetAndMutate ==
  /\ place # MeetingPlaceEmpty
  /\ \E c \in Creatures :
       /\ c # place
       /\ colorAndCount[c][1] # Faded
       /\ colorAndCount' = [colorAndCount EXCEPT
                             ![c] = <<Complement(colorAndCount[c][1], colorAndCount[place][1]), colorAndCount[c][2] + 1>,
                             ![place] = <<Complement(colorAndCount[c][1], colorAndCount[place][1]), colorAndCount[place][2] + 1>>]
       /\ grandTotal' = grandTotal + 1
       /\ place' = MeetingPlaceEmpty

Next == EnterPlace \/ Fade \/ MeetAndMutate

Spec == Init /\ [][Next]_vars

SumMet ==
  /\ (grandTotal = M) => SumCount(Creatures) = 2 * M

====