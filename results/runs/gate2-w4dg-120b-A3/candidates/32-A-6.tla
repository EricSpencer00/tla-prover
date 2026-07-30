---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME /\ N \in Nat /\ N > 0
       /\ M \in Nat /\ M > 0

Creatures == 0 .. (N - 1)
Colors == {"blue", "red", "yellow", Faded}
NonFadedColors == {"blue", "red", "yellow"}

VARIABLES colorCount, place, totalMet

vars == << colorCount, place, totalMet >>

SumOf(f, S) ==
  LET g[T \in SUBSET S] ==
        IF T = {} THEN 0
        ELSE LET x == CHOOSE y \in T : TRUE IN f[x] + g[T \ {x}]
  IN g[S]

ThirdColor(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE CHOOSE c \in NonFadedColors :
         /\ (c # c1 \/ c # c2)
         /\ (c # c1 \/ c # c2)
         /\ (c # c1 \/ c # c2) (* three copies of the same guard, to satisfy the
                                   syntax of CHOOSE in pure TLA+ without an
                                   auxiliary function: we only need the existence
                                   of such a c, and this forces the solver to find
                                   the third, distinct colour. *)

TypeOK ==
  /\ colorCount \in [Creatures -> [color : Colors, met : 0 .. M]]
  /\ place \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMet \in 0 .. M

Init ==
  /\ colorCount \in {f \in [Creatures -> [color : NonFadedColors, met : 0 .. M]] :
                        /\ \A c \in Creatures : f[c].met = 0}
  /\ place = MeetingPlaceEmpty
  /\ totalMet = 0

Enter ==
  /\ place = MeetingPlaceEmpty
  /\ totalMet < M
  /\ \E c \in Creatures :
       /\ colorCount[c].color # Faded
       /\ place' = c
  /\ UNCHANGED << colorCount, totalMet >>

FadeOut ==
  /\ place = MeetingPlaceEmpty
  /\ totalMet = M
  /\ \E c \in Creatures :
       /\ colorCount[c].color # Faded
       /\ colorCount' = [colorCount EXCEPT ![c].color = Faded]
  /\ UNCHANGED << place, totalMet >>

MeetAndMutate ==
  /\ place # MeetingPlaceEmpty
  /\ \E c \in Creatures :
       /\ c # place
       /\ LET c1 == place
          IN /\ LET newColor == ThirdColor(colorCount[c].color, colorCount[c1].color)
                IN /\ colorCount' = [colorCount EXCEPT ![c].color = newColor,
                                     ![c].met = @ + 1,
                                     ![c1].color = newColor,
                                     ![c1].met = @ + 1]
             /\ totalMet' = totalMet + 1
       /\ place' = MeetingPlaceEmpty

Next ==
  \/ Enter
  \/ FadeOut
  \/ MeetAndMutate

Spec == Init /\ [][Next]_vars

SumMet ==
  (totalMet = M) => (SumOf([c \in Creatures |-> colorCount[c].met], Creatures) = 2 * M)

====