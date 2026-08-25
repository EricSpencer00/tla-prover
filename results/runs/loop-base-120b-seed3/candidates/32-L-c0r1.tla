---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* ---------------------------------------------------------------------- *)
(* Colors *)
CONSTANT Blue, Red, Yellow
ColorSet == {Blue, Red, Yellow, Faded}
NonFadedColors == {Blue, Red, Yellow}

(* ---------------------------------------------------------------------- *)
(* Complement rule *)
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE
        CHOOSE x \in NonFadedColors :
            x # c1 /\ x # c2

(* ---------------------------------------------------------------------- *)
(* State variables *)
VARIABLES cmap, mall, gcnt

(* cmap : [1..N -> (ColorSet \X Nat)]  maps each creature to <<color, meetingCount>> *)
(* mall : either MeetingPlaceEmpty or the id of the waiting creature *)
(* gcnt : total number of completed meetings *)

(* ---------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ cmap \in [1..N -> (NonFadedColors \X {0})]
    /\ mall = MeetingPlaceEmpty
    /\ gcnt = 0

(* ---------------------------------------------------------------------- *)
(* Actions *)

Enter ==
    \E c \in 1..N :
        /\ mall = MeetingPlaceEmpty
        /\ gcnt < M
        /\ cmap[c][1] # Faded
        /\ mall' = c
        /\ cmap' = cmap
        /\ gcnt' = gcnt

Fade ==
    \E c \in 1..N :
        /\ mall = MeetingPlaceEmpty
        /\ gcnt >= M
        /\ cmap[c][1] # Faded
        /\ cmap' = [cmap EXCEPT ![c] = <<Faded, cmap[c][2]>>]
        /\ mall' = MeetingPlaceEmpty
        /\ gcnt' = gcnt

Meet ==
    \E c \in 1..N :
        /\ mall # MeetingPlaceEmpty
        /\ gcnt < M
        /\ c # mall
        /\ cmap[c][1] # Faded
        /\ cmap[mall][1] # Faded
        /\ cmap' = [cmap EXCEPT
                     ![c]   = <<Complement(cmap[c][1], cmap[mall][1]), cmap[c][2] + 1>>,
                     ![mall] = <<Complement(cmap[c][1], cmap[mall][1]), cmap[mall][2] + 1>>]
        /\ mall' = MeetingPlaceEmpty
        /\ gcnt' = gcnt + 1

Next == Enter \/ Fade \/ Meet

(* ---------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_<<cmap, mall, gcnt>>

(* ---------------------------------------------------------------------- *)
(* Invariants *)

TypeOK ==
    /\ cmap \in [1..N -> (ColorSet \X Nat)]
    /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
    /\ gcnt \in Nat

SumMet ==
    gcnt = M => (∑ i \in 1..N : cmap[i][2]) = 2 * M

(* ---------------------------------------------------------------------- *)
(* The identifiers required by the .cfg file *)
SPECIFICATION Spec
INVARIANT TypeOK, SumMet

====