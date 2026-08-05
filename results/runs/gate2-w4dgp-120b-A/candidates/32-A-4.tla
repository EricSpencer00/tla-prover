---- MODULE Chameneos ----
EXTENDS Integers

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Chameneos are identifed by numbers 1..N, but they are treated
\* symmetrically and the model must not depend on the order of the
\* identifiers.  Every creature carries one of the three colors or the
\* Faded marker once the meeting place has closed.

Creatures == 1..N
Colors == {blue, red, yellow}

VARIABLES attr, place, totalMet
vars == <<attr, place, totalMet>>

\* Complementation rule: two identical colors stay unchanged, two distinct
\* colors both become the third one.
Complement(a, b) ==
  IF a = b THEN a
  ELSE ({blue, red, yellow} \ {a, b}).choose

SumOfIndividualMeetings ==
  LET f[S \in SUBSET Creatures] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE
             IN attr[x][2] + f[S \ {x}]
  IN f[Creatures]

TypeOK ==
  /\ attr \in [Creatures -> (Colors \cup {Faded}) \X (0..M)]
  /\ place \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMet \in 0..M

Init ==
  /\ attr \in [Creatures -> (Colors \X {0})]
  /\ place = MeetingPlaceEmpty
  /\ totalMet = 0

\* The meeting place accepts one waiting creature at a time up to the
\* limit of M meetings.
EnterWaiting(c) ==
  /\ place = MeetingPlaceEmpty
  /\ totalMet < M
  /\ attr[c][1] # Faded
  /\ place' = c
  /\ UNCHANGED <<attr, totalMet>>

\* After M meetings the mall closes and a creature that tries to enter
\* simply fades out instead of waiting.
FadeOut(c) ==
  /\ place = MeetingPlaceEmpty
  /\ totalMet = M
  /\ attr[c][1] # Faded
  /\ attr' = [attr EXCEPT ![c] = <<Faded, @ [2]>>]
  /\ UNCHANGED <<place, totalMet>>

\* Two distinct creatures exchange colors and both count one more meeting.
\* The global counter advances once, so any two placements of the same
\* meeting must agree on the new color for both participants.
MeetAndMutate(d) ==
  /\ place # MeetingPlaceEmpty
  /\ place # d
  /\ totalMet < M
  /\ LET mcolor == Complement(attr[place][1], attr[d][1])
         in attr' = [attr EXCEPT ![place] = <<mcolor, @ [2] + 1>>,
                              ![d] = <<mcolor, @ [2] + 1>>]
  /\ place' = MeetingPlaceEmpty
  /\ totalMet' = totalMet + 1

Next ==
  \/ \E c \in Creatures : EnterWaiting(c) \/ FadeOut(c)
  \/ \E d \in Creatures : MeetAndMutate(d)

Spec == Init /\ [][Next]_vars

\* Every meeting involves exactly two participants, so when M meetings have
\* elapsed the individual tallies must add up to exactly 2*M.
SumMet == totalMet = M => SumOfIndividualMeetings = 2 * M

====