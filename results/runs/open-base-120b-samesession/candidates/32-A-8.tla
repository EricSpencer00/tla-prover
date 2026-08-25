---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* ----------------------------------------------------------------------
   Types and helper definitions
   ---------------------------------------------------------------------- *)

PrimaryColors == {"blue", "red", "yellow"}
ColorSet == PrimaryColors \cup {Faded}

Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE IF (c1 = "blue"  /\ c2 = "red")    \/ (c1 = "red"   /\ c2 = "blue")    THEN "yellow"
    ELSE IF (c1 = "blue"  /\ c2 = "yellow")\/ (c1 = "yellow"/\ c2 = "blue")   THEN "red"
    ELSE "blue"   \* the only remaining primary color

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)

VARIABLES creatures, mall, totalMeetings

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)

Init ==
    /\ creatures = [i \in 1..N |-> 
                      [color    |-> CHOOSE c \in PrimaryColors: TRUE,
                       meetCount|-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ totalMeetings = 0

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

Enter ==
    /\ totalMeetings < M
    /\ mall = MeetingPlaceEmpty
    /\ \E i \in 1..N :
          /\ creatures[i].color # Faded
          /\ mall' = i
          /\ UNCHANGED <<creatures, totalMeetings>>

FadeOut ==
    /\ totalMeetings >= M
    /\ mall = MeetingPlaceEmpty
    /\ \E i \in 1..N :
          /\ creatures[i].color # Faded
          /\ creatures' = [creatures EXCEPT ![i] = 
                               [color |-> Faded,
                                meetCount |-> creatures[i].meetCount]]
          /\ UNCHANGED <<mall, totalMeetings>>

Meet ==
    /\ totalMeetings < M
    /\ mall # MeetingPlaceEmpty
    /\ \E i \in 1..N :
          /\ i # mall
          /\ creatures[i].color # Faded
          /\ creatures[mall].color # Faded
          /\ LET newColor == Complement(creatures[i].color, creatures[mall].color) IN
                /\ creatures' = [creatures EXCEPT 
                                   ![i]   = [color |-> newColor,
                                             meetCount |-> creatures[i].meetCount + 1],
                                   ![mall]= [color |-> newColor,
                                             meetCount |-> creatures[mall].meetCount + 1]]
                /\ totalMeetings' = totalMeetings + 1
                /\ mall' = MeetingPlaceEmpty

Next == Enter \/ FadeOut \/ Meet

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<creatures, mall, totalMeetings>>

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)

TypeOK ==
    /\ creatures \in [1..N -> [color : ColorSet, meetCount : Nat]]
    /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in Nat

SumMet ==
    totalMeetings = M => (\Sum i \in 1..N: creatures[i].meetCount) = 2 * M

====