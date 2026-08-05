---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

CREATURES == 1..N
Colors == {"blue", "red", "yellow"}

VARIABLES attr, mall, met

vars == <<attr, mall, met>>

TypeOK ==
  /\ attr \in [CREATURES -> (Colors \cup {Faded}) \X (0..M)]
  /\ mall \in CREATURES \cup {MeetingPlaceEmpty}
  /\ met \in 0..M

\* Sum of individual meeting counts, taken over all creatures.
RECURSIVE MetTotal(_)
MetTotal(S) ==
  IF S = {} THEN 0
  ELSE LET c == CHOOSE x \in S : TRUE IN attr[c][2] + MetTotal(S \ {c})

\* A meeting always consumes two participants.
MeetingCountsCoherent == met = M => MetTotal(CREATURES) = 2 * M

Init ==
  /\ attr \in [CREATURES -> (Colors \X {0})]
  /\ mall = MeetingPlaceEmpty
  /\ met = 0

Enter(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ attr[c][1] # Faded
  /\ met < M
  /\ mall' = c
  /\ UNCHANGED <<attr, met>>

Fade(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ attr[c][1] # Faded
  /\ met >= M
  /\ attr' = [attr EXCEPT ![c] = <<Faded, @ [2]>>]
  /\ UNCHANGED <<mall, met>>

\* Complement rule over the three colors: two identical colors stay unchanged,
\* two distinct colors both become the third.
Complement(a, b) ==
  IF a = b THEN a
  ELSE (Colors \ {a, b}) = {c} => c

Meet(c) ==
  /\ mall # MeetingPlaceEmpty
  /\ mall # c
  /\ attr[mall][1] # Faded
  /\ LET newc == Complement(attr[c][1], attr[mall][1])
     IN attr' = [attr EXCEPT ![c] = <<newc, @ [2] + 1>>, ![mall] = <<newc, @ [2] + 1>>]
  /\ met' = met + 1
  /\ mall' = MeetingPlaceEmpty

Next ==
  \/ \E c \in CREATURES : Enter(c) \/ Fade(c) \/ Meet(c)

Spec == Init /\ [][Next]_vars

====