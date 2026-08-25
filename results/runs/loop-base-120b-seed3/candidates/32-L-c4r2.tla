---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* ---------------------------------------------------------------------- *)
(*  Sets and derived constants                                            *)
(* ---------------------------------------------------------------------- *)

Creatures == 1 .. N

BaseColors == {"blue", "red", "yellow"}

Colors == BaseColors \cup {Faded}

(* Upper bound for meeting counts of each creature *)
CountBound == 0 .. M

(* ---------------------------------------------------------------------- *)
(*  Variables                                                            *)
(* ---------------------------------------------------------------------- *)

VARIABLES creatures, place, total

(* ---------------------------------------------------------------------- *)
(*  Helper definitions                                                   *)
(* ---------------------------------------------------------------------- *)

Complement(c1, c2) ==
  IF c1 = c2
    THEN c1
    ELSE CHOOSE x \in BaseColors : x # c1 /\ x # c2

(* ---------------------------------------------------------------------- *)
(*  Recursive sum of the individual meeting counts                        *)
(* ---------------------------------------------------------------------- *)

RECURSIVE SumCountsFrom(_)

SumCountsFrom(i) ==
  IF i > N THEN 0
  ELSE creatures[i].count + SumCountsFrom(i + 1)

SumCounts == SumCountsFrom(1)

(* ---------------------------------------------------------------------- *)
(*  Initial state                                                        *)
(* ---------------------------------------------------------------------- *)

Init ==
  /\ creatures \in [Creatures -> [color : Colors, count : CountBound]]
  /\ \A c \in Creatures :
        /\ creatures[c].color \in BaseColors
        /\ creatures[c].count = 0
  /\ place = MeetingPlaceEmpty
  /\ total = 0

(* ---------------------------------------------------------------------- *)
(*  Actions                                                              *)
(* ---------------------------------------------------------------------- *)

Enter ==
  /\ place = MeetingPlaceEmpty
  /\ total < M
  /\ \E c \in Creatures :
        /\ creatures[c].color # Faded
        /\ place' = c
        /\ UNCHANGED <<creatures, total>>

FadeOut ==
  /\ place = MeetingPlaceEmpty
  /\ total = M
  /\ \E c \in Creatures :
        /\ creatures[c].color # Faded
        /\ creatures' = [creatures EXCEPT ![c].color = Faded]
        /\ UNCHANGED <<place, total>>

Meet ==
  /\ place \in Creatures
  /\ total < M
  /\ \E a \in Creatures :
        /\ a # place
        /\ creatures[a].color # Faded
        /\ creatures[place].color # Faded
        /\ LET newColor == Complement(creatures[a].color, creatures[place].color) IN
             /\ creatures' = [creatures EXCEPT
                               ![a].color   = newColor,
                               ![a].count   = @ + 1,
                               ![place].color = newColor,
                               ![place].count = @ + 1]
             /\ total' = total + 1
             /\ place' = MeetingPlaceEmpty

Next == \/ Enter \/ FadeOut \/ Meet

(* ---------------------------------------------------------------------- *)
(*  Specification                                                        *)
(* ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<creatures, place, total>>

(* ---------------------------------------------------------------------- *)
(*  Invariants                                                           *)
(* ---------------------------------------------------------------------- *)

TypeOK ==
  /\ creatures \in [Creatures -> [color : Colors, count : CountBound]]
  /\ place \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in CountBound

SumMet ==
  (total = M) => (SumCounts = 2 * M)

====