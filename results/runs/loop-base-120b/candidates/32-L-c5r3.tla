---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

VARIABLES cmap, mall, total

(* ---------------------------------------------------------------------- *)
(* Derived sets *)
Creatures == 1..N
Colors   == {"blue", "red", "yellow"}

(* ---------------------------------------------------------------------- *)
(* Complement rule *)
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE CHOOSE c \in Colors : c /= c1 /\ c /= c2

(* ---------------------------------------------------------------------- *)
(* Type invariant *)
TypeOK ==
  /\ cmap \in [Creatures -> [color : Colors \cup {Faded}, count : Nat]]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in Nat
  /\ total <= M

(* ---------------------------------------------------------------------- *)
(* Initial state *)
Init ==
  /\ cmap = [i \in Creatures |-> [color |-> CHOOSE col \in Colors : TRUE,
                                 count |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

(* ---------------------------------------------------------------------- *)
(* Actions *)

EnterEmpty ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ \E c \in Creatures :
        /\ cmap[c].color /= Faded
        /\ mall' = c
        /\ cmap' = cmap
        /\ total' = total

FadeOut ==
  /\ mall = MeetingPlaceEmpty
  /\ total = M
  /\ \E c \in Creatures :
        /\ cmap[c].color /= Faded
        /\ cmap' = [cmap EXCEPT ![c].color = Faded]
        /\ mall' = MeetingPlaceEmpty
        /\ total' = total

MeetAndMutate ==
  /\ mall /= MeetingPlaceEmpty
  /\ total < M
  /\ \E c2 \in Creatures :
        /\ c2 /= mall
        /\ cmap[c2].color /= Faded
        /\ LET c1 == mall,
               newCol == Complement(cmap[c1].color, cmap[c2].color)
           IN /\ cmap' = [cmap EXCEPT
                          ![c1] = [color |-> newCol,
                                   count |-> cmap[c1].count + 1],
                          ![c2] = [color |-> newCol,
                                   count |-> cmap[c2].count + 1]]
              /\ mall' = MeetingPlaceEmpty
              /\ total' = total + 1

Next ==
  \/ EnterEmpty
  \/ FadeOut
  \/ MeetAndMutate

(* ---------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_<<cmap, mall, total>>

(* ---------------------------------------------------------------------- *)
(* Safety invariant about total meetings *)
SumMet ==
  (total = M) => (∑ i \in Creatures : cmap[i].count = 2 * M)

=============================================================================