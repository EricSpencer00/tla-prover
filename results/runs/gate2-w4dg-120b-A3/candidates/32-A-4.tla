---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N > 0 /\ M \in Nat /\ M > 0

Creatures == 1 .. N
Colors == {"blue", "red", "yellow"}

VARIABLES colour, waiting, totalMeetings

vars == << colour, waiting, totalMeetings >>

RECURSIVE SumF(_, _)
SumF(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumF(f, S \ {x})

TypeOK ==
  /\ colour \in [ Creatures -> [ hue : Colors \cup {Faded}, meets : 0 .. M ] ]
  /\ waiting \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0 .. M

InitColour(c) ==
  \/ [ hue |-> "blue", meets |-> 0 ]
  \/ [ hue |-> "red", meets |-> 0 ]
  \/ [ hue |-> "yellow", meets |-> 0 ]

Init ==
  /\ colour = [ c \in Creatures |-> InitColour(c) ]
  /\ waiting = MeetingPlaceEmpty
  /\ totalMeetings = 0

Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE LET S == { c1, c2 } IN CHOOSE c \in Colors : Colors \ S = {c}

Enter(c) ==
  /\ waiting = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ colour[c].hue # Faded
  /\ waiting' = c
  /\ UNCHANGED << colour, totalMeetings >>

Fade(c) ==
  /\ waiting = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ colour[c].hue # Faded
  /\ colour' = [ colour EXCEPT ![c].hue = Faded ]
  /\ UNCHANGED << waiting, totalMeetings >>

Meet(c) ==
  /\ waiting # MeetingPlaceEmpty
  /\ c # waiting
  /\ colour[c].hue # Faded
  /\ colour[waiting].hue # Faded
  /\ colour' = [ colour EXCEPT ![c] = [ hue |-> Complement(colour[c].hue, colour[waiting].hue), meets |-> colour[c].meets + 1 ],
                            ![waiting] = [ hue |-> Complement(colour[c].hue, colour[waiting].hue), meets |-> colour[waiting].meets + 1 ] ]
  /\ totalMeetings' = totalMeetings + 1
  /\ waiting' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : Enter(c)
  \/ \E c \in Creatures : Fade(c)
  \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

SumMet ==
  (totalMeetings = M) => (SumF([ c \in Creatures |-> colour[c].meets ], Creatures) = 2 * M)

====