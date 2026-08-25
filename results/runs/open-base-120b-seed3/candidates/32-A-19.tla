---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences, Integers

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* --------------------------------------------------------------------- *)
(* Colors *)
CONSTANT Blue, Red, Yellow

Colors       == {Blue, Red, Yellow}
AllColors    == Colors \cup {Faded}

(* --------------------------------------------------------------------- *)
(* State variables *)

VARIABLES Creatures, MeetingPlace, totalMeetings

(* --------------------------------------------------------------------- *)
(* Complement rule *)

Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CHOOSE c \in Colors : c # c1 /\ c # c2

(* --------------------------------------------------------------------- *)
(* Type invariant *)

TypeOK ==
  /\ Creatures \in [1..N -> (AllColors \X Nat)]
  /\ MeetingPlace \in (1..N) \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in Nat
  /\ totalMeetings <= M

(* --------------------------------------------------------------------- *)
(* Initial state *)

Init ==
  /\ \E cs \in [1..N -> Colors] :
        Creatures = [i \in 1..N |-> <<cs[i], 0>>]
  /\ MeetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

(* --------------------------------------------------------------------- *)
(* Actions *)

Enter ==
  /\ MeetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ \E c \in 1..N :
        /\ Creatures[c][1] # Faded
        /\ MeetingPlace' = c
        /\ Creatures' = Creatures
        /\ totalMeetings' = totalMeetings

Fade ==
  /\ MeetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ \E c \in 1..N :
        /\ Creatures[c][1] # Faded
        /\ Creatures' = [i \in 1..N |-> IF i = c THEN <<Faded, Creatures[i][2]>> ELSE Creatures[i]]
        /\ MeetingPlace' = MeetingPlaceEmpty
        /\ totalMeetings' = totalMeetings

Meet ==
  /\ MeetingPlace = p
  /\ p \in 1..N
  /\ totalMeetings < M
  /\ \E a \in 1..N :
        /\ a # p
        /\ Creatures[a][1] # Faded
        /\ LET c1       == Creatures[p][1]
               c2       == Creatures[a][1]
               newColor == Complement(c1, c2) IN
           /\ Creatures' = [i \in 1..N |-> 
                IF i = p THEN <<newColor, Creatures[i][2] + 1>>
                ELSE IF i = a THEN <<newColor, Creatures[i][2] + 1>>
                ELSE Creatures[i]]
           /\ totalMeetings' = totalMeetings + 1
           /\ MeetingPlace' = MeetingPlaceEmpty

Next == Enter \/ Fade \/ Meet

(* --------------------------------------------------------------------- *)
(* Specification *)

Spec == Init /\ [][Next]_<<Creatures, MeetingPlace, totalMeetings>>

(* --------------------------------------------------------------------- *)
(* Safety invariant *)

SumMet ==
  IF totalMeetings = M THEN
    Sum({ Creatures[i][2] : i \in 1..N }) = 2 * M
  ELSE
    TRUE

====