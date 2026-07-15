---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences

(*--------------------------------------------------------------------
  Constants (to be instantiated in the .cfg file)
--------------------------------------------------------------------*)
CONSTANT N          \* number of creatures
CONSTANT M          \* total meeting limit
CONSTANT Faded      \* the special faded color
CONSTANT MeetingPlaceEmpty \* special value meaning the meeting place is empty

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
Colors == {"blue", "red", "yellow", Faded}
Creatures == 1 .. N
NoOccupant == MeetingPlaceEmpty

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
\* Complement rule: given two (possibly equal) colors, return the resulting
\* color after a meeting.  If both are the same non‑faded color, they keep it.
\* If they are different non‑faded colors, both become the third color.
\* If either is Faded, the result is Faded (should never happen in a meeting).
Complement(c1, c2) ==
  IF c1 = Faded \/ c2 = Faded THEN Faded
  ELSE IF c1 = c2 THEN c1
  ELSE
    LET third == {"blue", "red", "yellow"} \ {c1, c2} IN
      IF Len(third) = 1 THEN CHOOSE x \in third : TRUE
      ELSE Faded  \* unreachable, defensive

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES colorMap, meetCount, meetingPlace, totalMeetings

(*--------------------------------------------------------------------
  Type definition (used for the TypeOK invariant)
--------------------------------------------------------------------*)
TypeOK ==
  /\ colorMap \in [Creatures -> Colors]
  /\ meetCount \in [Creatures -> Nat]
  /\ meetingPlace \in (Creatures \cup {MeetingPlaceEmpty})
  /\ totalMeetings \in Nat

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ colorMap = [c \in Creatures |-> CHOOSE col \in {"blue","red","yellow"} : TRUE]
     \* nondeterministically assign one of the three non‑faded colors
  /\ meetCount = [c \in Creatures |-> 0]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0
  /\ TypeOK

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)

Enter ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ \E c \in Creatures :
        /\ colorMap[c] # Faded
        /\ meetingPlace' = c
        /\ UNCHANGED << colorMap, meetCount, totalMeetings >>

FadeOut ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ \E c \in Creatures :
        /\ colorMap[c] # Faded
        /\ colorMap' = [colorMap EXCEPT ![c] = Faded]
        /\ totalMeetings' = totalMeetings + 1
        /\ UNCHANGED << meetCount, meetingPlace >>

MeetAndMutate ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ \E cArriving \in Creatures :
        /\ colorMap[cArriving] # Faded
        /\ cArriving # meetingPlace
        /\ LET cWaiting == meetingPlace IN
            /\ colorMap' = [colorMap EXCEPT
                  ![cArriving] = Complement(colorMap[cArriving], colorMap[cWaiting]),
                  ![cWaiting]   = Complement(colorMap[cArriving], colorMap[cWaiting])]
            /\ meetCount' = [meetCount EXCEPT
                  ![cArriving] = meetCount[cArriving] + 1,
                  ![cWaiting]   = meetCount[cWaiting]   + 1]
            /\ totalMeetings' = totalMeetings + 1
            /\ meetingPlace' = MeetingPlaceEmpty

Terminate ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ \A c \in Creatures : colorMap[c] = Faded
  /\ UNCHANGED << colorMap, meetCount, meetingPlace, totalMeetings >>

Next ==
  \/ Enter
  \/ FadeOut
  \/ MeetAndMutate
  \/ Terminate

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<colorMap, meetCount, meetingPlace, totalMeetings>>

(*--------------------------------------------------------------------
  Safety invariant: sum of individual meeting counts equals twice the
  total number of meetings once the limit has been reached.
--------------------------------------------------------------------*)
SumMet ==
  totalMeetings >= M => 
    ( \A c \in Creatures : meetCount[c] = meetCount'??? )   \* placeholder, see below

(* The intended invariant is:
   SumMet == totalMeetings >= M => 
               ( \sum_{c \in Creatures} meetCount[c] = 2 * M )
   However, TLA+ does not have built‑in summation over a set, so we define it:
*)

SumMet ==
  totalMeetings >= M => 
    ( \* sum of meetCount over all creatures
      LET s == { meetCount[c] : c \in Creatures } IN
        IF Cardinality(Creatures) = 0 THEN TRUE
        ELSE 
          (* Since each entry is a natural number, we can use the built‑in Sum *)
          ( \A n \in Nat : n \in s => TRUE ) /\ 
          ( \E sum \in Nat :
                sum = Sum({meetCount[c] : c \in Creatures}) /\ sum = 2 * M) )

(* However, the module Naturals does not define a generic Sum over a set.
   To avoid external definitions, we implement the sum using recursion. *)

(* Recursive definition of sum over a finite set of creatures *)
SumMeetings == 
  IF {} = {} THEN 0
  ELSE
    LET rec(S) == 
          IF S = {} THEN 0
          ELSE LET c == CHOOSE x \in S : TRUE IN 
               meetCount[c] + rec(S \ {c})
    IN rec(Creatures)

SumMet ==
  totalMeetings >= M => SumMeetings = 2 * M

(*--------------------------------------------------------------------
  The module must expose the identifiers required by the configuration:
--------------------------------------------------------------------*)
THEOREM SpecTypeOK == Spec => []TypeOK

=============================================================================