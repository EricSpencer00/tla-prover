---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* --------------------------------------------------------------------- *)
(* Basic sets *)

Creatures == 1..N

Blue   == "Blue"
Red    == "Red"
Yellow == "Yellow"

Colors == {Blue, Red, Yellow, Faded}

(* --------------------------------------------------------------------- *)
(* Complement rule *)

Complement(c1, c2) ==
  CASE c1 = c2 -> c1
  [] (c1 = Blue  /\ c2 = Red)    \/ (c1 = Red    /\ c2 = Blue)    -> Yellow
  [] (c1 = Blue  /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Blue)   -> Red
  [] (c1 = Red   /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Red)    -> Blue

(* --------------------------------------------------------------------- *)
(* Variables *)

VARIABLES st, place, totalMeetings

vars == <<st, place, totalMeetings>>

(* --------------------------------------------------------------------- *)
(* Type invariant *)

TypeOK ==
  /\ st \in [Creatures -> [color : Colors, count : Nat]]
  /\ place \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in Nat
  /\ totalMeetings <= M

(* --------------------------------------------------------------------- *)
(* Sum of meeting counts invariant *)

SumCounts ==
  IF Creatures = {} THEN 0
  ELSE
    LET f == [i \in Creatures |-> st[i].count] IN
      Sum(f)

SumMet ==
  totalMeetings = M => SumCounts = 2 * M

(* --------------------------------------------------------------------- *)
(* Initial state *)

Init ==
  /\ \E col \in [Creatures -> {Blue, Red, Yellow}] :
        st = [i \in Creatures |-> [color |-> col[i], count |-> 0]]
  /\ place = MeetingPlaceEmpty
  /\ totalMeetings = 0

(* --------------------------------------------------------------------- *)
(* Actions *)

Enter(i) ==
  /\ place = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ st[i].color # Faded
  /\ place' = i
  /\ UNCHANGED <<st, totalMeetings>>

Fade(i) ==
  /\ place = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ st[i].color # Faded
  /\ st' = [st EXCEPT ![i].color = Faded]
  /\ UNCHANGED <<place, totalMeetings>>

Meet(i) ==
  LET j == place IN
    /\ j # MeetingPlaceEmpty
    /\ i # j
    /\ totalMeetings < M
    /\ st[i].color # Faded
    /\ st[j].color # Faded
    /\ LET newC == Complement(st[i].color, st[j].color) IN
         /\ st' = [st EXCEPT
                    ![i] = [color |-> newC, count |-> @.count + 1],
                    ![j] = [color |-> newC, count |-> @.count + 1]]
         /\ totalMeetings' = totalMeetings + 1
         /\ place' = MeetingPlaceEmpty

Next ==
  \/ \E i \in Creatures : Enter(i)
  \/ \E i \in Creatures : Fade(i)
  \/ \E i \in Creatures : Meet(i)

(* --------------------------------------------------------------------- *)
(* Specification *)

Spec == Init /\ [][Next]_vars

====