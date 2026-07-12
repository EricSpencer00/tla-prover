---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    N          \* number of creatures (positive natural number)
    M          \* maximum number of meetings (positive natural number)
    Faded      \* the special faded color
    MeetingPlaceEmpty \* the special value indicating the meeting place is empty

(* ----------------------------------------------------------------------
   Derived constants
   ---------------------------------------------------------------------- *)

Creatures == 1..N
Colors== { "Blue", "Red", "Yellow" } \cup {Faded}
\* Total set of colors includes faded

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)

VARIABLES
    CreatureInfo,   \* mapping from each creature to [color : Color, meetings : Nat]
    MeetingPlace,   \* either MeetingPlaceEmpty or a creature identifier
    TotalMeetings   \* global counter of completed meetings

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)

(* Complement rule: if two colors are the same, return that color; otherwise
   return the third color not equal to either *)
Complement(c1, c2) ==
    IF c1 = c2
    THEN c1
    ELSE
        LET rest == { "Blue", "Red", "Yellow" } \ {c1, c2}
        IN
            IF Cardinality(rest) = 1
            THEN CHOOSE x \in rest : x
            ELSE Faded   \* should never happen if colors are valid

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Init ==
    /\ CreatureInfo = [c \in Creatures |-> [color |-> CHOOSE x \in { "Blue", "Red", "Yellow" } : x,
                        meetings |-> 0]]
    /\ MeetingPlace = MeetingPlaceEmpty
    /\ TotalMeetings = 0

EnterEmpty ==
    /\ MeetingPlace = MeetingPlaceEmpty
    /\ TotalMeetings < M
    /\ \E c \in Creatures :
          /\ CreatureInfo[c].color # Faded
          /\ MeetingPlace' = c
          /\ UNCHANGED << CreatureInfo, TotalMeetings >>

FadeOut ==
    /\ MeetingPlace = MeetingPlaceEmpty
    /\ TotalMeetings >= M
    /\ \E c \in Creatures :
          /\ CreatureInfo[c].color # Faded
          /\ CreatureInfo' = [CreatureInfo EXCEPT ![c].color = Faded]
          /\ UNCHANGED << MeetingPlace, TotalMeetings >>

MeetAndMutate ==
    /\ MeetingPlace \in Creatures
    /\ \E c \in Creatures :
          /\ c # MeetingPlace
          /\ \E newColor == Complement(CreatureInfo[MeetingPlace].color,
                                      CreatureInfo[c].color) :
                /\ CreatureInfo' = [CreatureInfo EXCEPT
                       ![MeetingPlace].color = newColor,
                       ![MeetingPlace].meetings = CreatureInfo[MeetingPlace].meetings + 1,
                       ![c].color = newColor,
                       ![c].meetings = CreatureInfo[c].meetings + 1]
                /\ MeetingPlace' = MeetingPlaceEmpty
                /\ TotalMeetings' = TotalMeetings + 1

Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate

Spec == Init /\ [][Next]_<<CreatureInfo, MeetingPlace, TotalMeetings>>

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)

TypeOK ==
    /\ CreatureInfo \in [Creatures -> [color : Colors, meetings : Nat]]
    /\ MeetingPlace \in Creatures \/ {MeetingPlaceEmpty}
    /\ TotalMeetings \in Nat
    /\ TotalMeetings <= M

(* ----------------------------------------------------------------------
   Safety invariant: after reaching the maximum number of meetings,
   the sum of all individual meeting counts equals twice M
   ---------------------------------------------------------------------- *)

SumMet ==
    (\A c \in Creatures : CreatureInfo[c].meetings) = 2 * TotalMeetings

====