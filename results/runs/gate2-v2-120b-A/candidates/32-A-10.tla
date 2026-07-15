---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* --colors and complement rule-- *)
Colors == {"blue", "red", "yellow", Faded}
NonFadedColors == {"blue", "red", "yellow"}

(* Complement function: given two colors, returns the new color after meeting *)
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE IF (c1 = "blue" /\ c2 = "red") \/ (c1 = "red" /\ c2 = "blue") THEN "yellow"
    ELSE IF (c1 = "blue" /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "blue") THEN "red"
    ELSE IF (c1 = "red" /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "red") THEN "blue"
    ELSE Faded \* should never happen for non‑faded inputs

(* Set of creature identifiers *)
Creatures == 1..N

VARIABLES state, meetingPlace, total

(* state maps each creature to a pair <<color, count>> *)
(* meetingPlace is either MeetingPlaceEmpty or a creature identifier *)
(* total is the global meeting counter *)
vars == <<state, meetingPlace, total>>

(* Helper to retrieve a creature's color and count *)
Color(c) == state[c][1]
Count(c) == state[c][2]

(* Initial predicate *)
Init ==
    /\ state = [c \in Creatures |-> <<CHOOSE col \in NonFadedColors : TRUE, 0>>]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ total = 0

(* Action: a non‑faded creature enters an empty meeting place *)
Enter(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ total < M
    /\ c \in Creatures
    /\ Color(c) # Faded
    /\ meetingPlace' = c
    /\ UNCHANGED <<state, total>>

(* Action: a non‑faded creature tries to enter after the limit and fades out *)
Fade(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ total >= M
    /\ c \in Creatures
    /\ Color(c) # Faded
    /\ state' = [state EXCEPT ![c] = <<Faded, Count(c)>>]
    /\ UNCHANGED <<meetingPlace, total>>

(* Action: two different creatures meet and mutate *)
MeetAndMutate(c) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ c \in Creatures
    /\ c # meetingPlace
    /\ Color(c) # Faded
    /\ Color(meetingPlace) # Faded
    /\ LET newCol == Complement(Color(c), Color(meetingPlace)) IN
       /\ state' = [state EXCEPT
                     ![c] = <<newCol, Count(c) + 1>>,
                     ![meetingPlace] = <<newCol, Count(meetingPlace) + 1>>]
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ total' = total + 1

(* No‑op action for stuttering *)
Stutter ==
    UNCHANGED vars

(* Next-state relation *)
Next ==
    \/ \E c \in Creatures : Enter(c)
    \/ \E c \in Creatures : Fade(c)
    \/ \E c \in Creatures : MeetAndMutate(c)
    \/ Stutter

(* Specification *)
Spec == Init /\ [][Next]_vars

(* Type correctness invariant *)
TypeOK ==
    /\ state \in [Creatures -> <<Colors, Nat>>]
    /\ meetingPlace \in {MeetingPlaceEmpty} \cup Creatures
    /\ total \in Nat

(* Safety invariant: sum of individual counts equals twice the total meetings when limit reached *)
SumMet ==
    total >= M => 
        \A c \in Creatures : Count(c) = 
            (total * 2) \div N + 
            (IF (total * 2) % N = 0 THEN 0 ELSE 
                IF c <= ((total * 2) % N) THEN 1 ELSE 0)

(* Theorems to expose the required identifiers for the .cfg file *)
THEOREM SpecIsSpec == Spec
THEOREM TypeOKInv == TypeOK
THEOREM SumMetInv == SumMet

====