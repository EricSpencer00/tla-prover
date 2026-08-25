---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

(*--------------------------------------------------------------------
  Constants (provided by the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS N, M, Faded, MeetingPlaceEmpty

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
Creatures == 1..N

ColorsNoFaded == {"blue", "red", "yellow"}
Colors == ColorsNoFaded \cup {Faded}

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES info, mall, totalMeetings

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Complement(col1, col2) ==
  IF col1 = col2 THEN
    col1
  ELSE
    CHOOSE c \in ColorsNoFaded : c # col1 /\ c # col2

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ info \in [Creatures -> [color : ColorsNoFaded, cnt : Nat]]
  /\ \A c \in Creatures : info[c].cnt = 0
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings = 0

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
Enter(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ info[c].color # Faded
  /\ mall' = c
  /\ info' = info
  /\ totalMeetings' = totalMeetings

Fade(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ info[c].color # Faded
  /\ info' = [info EXCEPT ![c].color = Faded]
  /\ mall' = MeetingPlaceEmpty
  /\ totalMeetings' = totalMeetings

Meet ==
  \E w \in Creatures :
    /\ mall = w
    /\ \E c \in Creatures :
         /\ c # w
         /\ info[w].color # Faded
         /\ info[c].color # Faded
         /\ totalMeetings < M
         /\ LET newcol == Complement(info[w].color, info[c].color) IN
              /\ info' = [info EXCEPT
                             ![w].color = newcol,
                             ![c].color = newcol,
                             ![w].cnt   = @ + 1,
                             ![c].cnt   = @ + 1]
              /\ totalMeetings' = totalMeetings + 1
              /\ mall' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : Enter(c)
  \/ \E c \in Creatures : Fade(c)
  \/ Meet

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec ==
  Init /\ [][Next]_<<info, mall, totalMeetings>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeOK ==
  /\ info \in [Creatures -> [color : Colors, cnt : Nat]]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in Nat

SumMet ==
  totalMeetings = M => 
    (\Sum c \in Creatures : info[c].cnt) = 2 * M

=============================================================================