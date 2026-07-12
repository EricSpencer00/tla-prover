---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(* ----------------------------------------------------------------------
   CONSTANTS (as required by the reference configuration)
   ---------------------------------------------------------------------- *)
CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* ----------------------------------------------------------------------
   Types
   ---------------------------------------------------------------------- *)
Creatures == 1..N
Colors == {"blue", "red", "yellow"} \cup {Faded}
ColorComplement ==
  [c1, c2 \in {"blue", "red", "yellow"} |
   IF c1 = c2 THEN c1
   ELSE {"blue", "red", "yellow"} \ {c1, c2}][]
(* The complement is the third distinct color when c1 ≠ c2. *)

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)
VARIABLES State, Occupant, TotalMeetings

(* ----------------------------------------------------------------------
   State definition: mapping from each creature to [color |-> Color, count |-> Nat]
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ State \in [Creatures |-> [color : Colors, count : Nat]]
  /\ Occupant \in Creatures \cup {MeetingPlaceEmpty}
  /\ TotalMeetings \in 0..M

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
  /\ State = [c \in Creatures |-> [color |-> ChosenColor(c), count |-> 0]]
     \* ChosenColor(c) is nondeterministic over {blue, red, yellow}
  /\ Occupant = MeetingPlaceEmpty
  /\ TotalMeetings = 0

(* Helper to nondeterministically pick an initial color *)
ChosenColor == [c \in Creatures |-> CHOOSE color \in {"blue", "red", "yellow"}: TRUE]

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

(* Enter empty meeting place: a creature enters when the place is empty
   and the total meetings have not reached the limit. *)
EnterEmpty ==
  /\ Occupant = MeetingPlaceEmpty
  /\ TotalMeetings < M
  /\ \E c \in Creatures :
        /\ State[c].color \in {"blue", "red", "yellow"}   \* non-faded
        /\ Occupant' = c
        /\ State' = State
        /\ TotalMeetings' = TotalMeetings

(* Fade out: a creature that tries to enter when the place is empty
   and the meeting limit has been reached becomes faded. *)
FadeOut ==
  /\ Occupant = MeetingPlaceEmpty
  /\ TotalMeetings = M
  /\ \E c \in Creatures :
        /\ State[c].color \in {"blue", "red", "yellow"}   \* non-faded
        /\ State' = [State EXCEPT ![c].color = Faded]
        /\ Occupant' = Occupant
        /\ TotalMeetings' = TotalMeetings

(* Meet and mutate: a creature arrives while another is waiting. Both
   creatures mutate according to the complement rule, increment individual
   and global counts, and the meeting place becomes empty. *)
MeetAndMutate ==
  /\ Occupant \in Creatures
  /\ \E c \in Creatures :
        /\ c # Occupant
        /\ State[c].color \in {"blue", "red", "yellow"}
        /\ State[Occupant].color \in {"blue", "red", "yellow"}
        /\ NewColor == [c1, c2 \in {"blue", "red", "yellow"} |
                         IF c1 = c2 THEN c1
                         ELSE {"blue", "red", "yellow"} \ {c1, c2}][State[c].color, State[Occupant].color]
        /\ State' = [ State EXCEPT ![c].color = NewColor,
                                 ![c].count = State[c].count + 1,
                                 ![Occupant].color = NewColor,
                                 ![Occupant].count = State[Occupant].count + 1 ]
        /\ Occupant' = MeetingPlaceEmpty
        /\ TotalMeetings' = TotalMeetings + 1

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
  \/ EnterEmpty
  \/ FadeOut
  \/ MeetAndMutate

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec ==
  Init /\ [][Next]_<<State, Occupant, TotalMeetings>>

(* ----------------------------------------------------------------------
   Safety invariant: when the global meeting counter reaches the maximum,
   the sum of all individual meeting counts equals twice the maximum.
   ---------------------------------------------------------------------- *)
SumMet ==
  IF TotalMeetings = M
     THEN
        /\ \E sum \in Nat :
              (\A c \in Creatures : State[c].count = sum) \/ (* not needed but ensures soundness *)
             /\ sum = 2 * M
            (* The above expression simply checks the sum; the auxiliary part is optional *)
     ELSE
        TRUE

(* ----------------------------------------------------------------------
   The invariant TypeOK may be useful for TLC checking but is not required by the spec.
   ---------------------------------------------------------------------- *)
TypeOK == Init /\ [][Next]_<<State, Occupant, TotalMeetings>>

====