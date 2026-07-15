---- MODULE Chameneos ----
EXTENDS Naturals, TLC

(*---------------------------------------------------------------------*)
(* Constants                                                          *)
(*---------------------------------------------------------------------*)
CONSTANT N           \* Number of creatures (positive natural)
CONSTANT M           \* Total number of meetings allowed (positive natural)
CONSTANT Faded       \* Symbol representing a faded creature
CONSTANT MeetingPlaceEmpty \* Symbol representing an empty meeting place

(*---------------------------------------------------------------------*)
(* Enumerated sets                                                    *)
(*---------------------------------------------------------------------*)
Colors == {"blue", "red", "yellow", Faded}
BaseColors == {"blue", "red", "yellow"}

(*---------------------------------------------------------------------*)
(* Variables                                                          *)
(*---------------------------------------------------------------------*)
VARIABLES
    creatures,      \* Mapping: creature id -> [color : Colors, meetCount : Nat]
    meetingPlace,   \* Either MeetingPlaceEmpty or a creature id
    totalMet        \* Global meeting counter

(*---------------------------------------------------------------------*)
(* Helper definitions                                                 *)
(*---------------------------------------------------------------------*)
CreaturesSet == 1 .. N

(* Complement (mutation) rule for two colors *)
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE
        CASE c1 = "blue"  /\ c2 = "red"    : "yellow" []
         [] c1 = "blue"  /\ c2 = "yellow": "red"    []
         [] c1 = "red"   /\ c2 = "blue"   : "yellow" []
         [] c1 = "red"   /\ c2 = "yellow": "blue"    []
         [] c1 = "yellow"/\ c2 = "blue"   : "red"    []
         [] c1 = "yellow"/\ c2 = "red"    : "blue"   []
         [] OTHER                         : c1  \* Should not occur

(* Sum of all individual meeting counts *)
SumMeetingCounts ==
    \Sum i \in CreaturesSet : creatures[i].meetCount

(*---------------------------------------------------------------------*)
(* Initial state                                                      *)
(*---------------------------------------------------------------------*)
Init ==
    /\ creatures = [i \in CreaturesSet |-> [color |-> CHOOSE c \in BaseColors : TRUE,
                                           meetCount |-> 0]]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet = 0

(*---------------------------------------------------------------------*)
(* Actions                                                            *)
(*---------------------------------------------------------------------*)

EnterEmpty ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet < M
    /\ \E c \in CreaturesSet :
          /\ creatures[c].color # Faded
          /\ meetingPlace' = c
          /\ UNCHANGED <<creatures, totalMet>>

FadeOut ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMet >= M
    /\ \E c \in CreaturesSet :
          /\ creatures[c].color # Faded
          /\ creatures' = [creatures EXCEPT ![c].color = Faded]
          /\ UNCHANGED <<meetingPlace, totalMet>>

MeetAndMutate ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ totalMet < M
    /\ \E newC \in CreaturesSet :
          /\ newC # meetingPlace
          /\ creatures[newC].color # Faded
          /\ LET waiting == meetingPlace IN
                /\ LET newColor == Complement(creatures[waiting].color,
                                             creatures[newC].color) IN
                /\ creatures' = [creatures EXCEPT
                                   ![waiting].color = newColor,
                                   ![waiting].meetCount = @ + 1,
                                   ![newC].color = newColor,
                                   ![newC].meetCount = @ + 1]
                /\ meetingPlace' = MeetingPlaceEmpty
                /\ totalMet' = totalMet + 1

\* No other state changes are allowed
Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate

(*---------------------------------------------------------------------*)
(* Specification                                                      *)
(*---------------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<creatures, meetingPlace, totalMet>>

(*---------------------------------------------------------------------*)
(* Type correctness invariant (optional but useful)                   *)
(*---------------------------------------------------------------------*)
TypeOK ==
    /\ meetingPlace \in CreaturesSet \cup {MeetingPlaceEmpty}
    /\ totalMet \in Nat
    /\ creatures \in [CreaturesSet -> [color : Colors,
                                        meetCount : Nat]]

(*---------------------------------------------------------------------*)
(* Safety invariant: sum of individual counts equals 2 * totalMet    *)
(*---------------------------------------------------------------------*)
SumMet ==
    SumMeetingCounts = 2 * totalMet

=============================================================================