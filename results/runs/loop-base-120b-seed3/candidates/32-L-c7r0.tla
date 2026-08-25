---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(* --------------------------------------------------------------------- *)
(* Sets and helper definitions                                            *)

Creatures == 1 .. N

Colors == {"blue", "red", "yellow", Faded}
BaseColors == {"blue", "red", "yellow"}

(* Complement rule: if the two colors are equal keep it, otherwise return the
   third base color. *)
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CASE /\ c1 = "blue"  /\ c2 = "red"
       \/ /\ c1 = "red"   /\ c2 = "blue"   -> "yellow"
       \/ /\ c1 = "blue"  /\ c2 = "yellow" -> "red"
       \/ /\ c1 = "yellow"/\ c2 = "blue"   -> "red"
       \/ /\ c1 = "red"   /\ c2 = "yellow" -> "blue"
       \/ /\ c1 = "yellow"/\ c2 = "red"   -> "blue"
       [] OTHER -> Faded   \* should never happen

(* --------------------------------------------------------------------- *)
(* State variables                                                       *)

VARIABLES st, mall, total

(* --------------------------------------------------------------------- *)
(* Type invariant                                                         *)

TypeOK ==
  /\ st \in [Creatures -> [color : Colors, count : Nat]]
  /\ mall \in (Creatures \cup {MeetingPlaceEmpty})
  /\ total \in Nat

(* --------------------------------------------------------------------- *)
(* Initial state                                                          *)

Init ==
  /\ st \in [Creatures -> [color : BaseColors, count : Nat]]
  /\ \A c \in Creatures: st[c].count = 0
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

(* --------------------------------------------------------------------- *)
(* Actions *)

Enter(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ c \in Creatures
  /\ st[c].color # Faded
  /\ mall' = c
  /\ UNCHANGED <<st, total>>

Fade(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ total >= M
  /\ c \in Creatures
  /\ st[c].color # Faded
  /\ st' = [st EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<mall, total>>

Meet(c) ==
  /\ mall # MeetingPlaceEmpty
  /\ total < M
  /\ c \in Creatures
  /\ c # mall
  /\ st[c].color # Faded
  /\ st[mall].color # Faded
  /\ LET w == mall IN
        newColor == Complement(st[c].color, st[w].color) IN
        st' = [st EXCEPT
                ![c] = [color |-> newColor,
                        count |-> @.count + 1],
                ![w] = [color |-> newColor,
                        count |-> @.count + 1]]
  /\ total' = total + 1
  /\ mall' = MeetingPlaceEmpty

Next ==
  \E c \in Creatures: Enter(c) \/ Fade(c) \/ Meet(c)

(* --------------------------------------------------------------------- *)
(* Specification                                                          *)

Spec ==
  Init /\ [][Next]_<<st, mall, total>>

(* --------------------------------------------------------------------- *)
(* Safety property: sum of individual meeting counts when total = M       *)

SumMet ==
  IF total = M THEN
    Sum({ st[c].count : c \in Creatures }) = 2 * M
  ELSE TRUE

(* --------------------------------------------------------------------- *)
(* Invariants to be checked                                                *)

INVARIANTS == TypeOK /\ SumMet

====