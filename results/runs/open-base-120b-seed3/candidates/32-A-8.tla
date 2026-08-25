---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N, M, Faded, MeetingPlaceEmpty

(* --------------------------------------------------------------------- *)
(*  Colors and complement rule                                           *)
(* --------------------------------------------------------------------- *)

Color == {"blue", "red", "yellow", Faded}
NonFadedColor == {"blue", "red", "yellow"}

Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE
    CASE c1 = "blue" /\ c2 = "red"    : "yellow"
       [] c1 = "red"  /\ c2 = "blue"   : "yellow"
       [] c1 = "blue" /\ c2 = "yellow" : "red"
       [] c1 = "yellow" /\ c2 = "blue" : "red"
       [] c1 = "red"  /\ c2 = "yellow" : "blue"
       [] c1 = "yellow" /\ c2 = "red"  : "blue"
       [] OTHER                        : Faded

(* --------------------------------------------------------------------- *)
(*  Variables                                                            *)
(* --------------------------------------------------------------------- *)

VARIABLES state, mall, total

(* --------------------------------------------------------------------- *)
(*  Initialization                                                       *)
(* --------------------------------------------------------------------- *)

Init ==
  /\ state \in [1..N -> [color : Color, cnt : Nat]]
  /\ \A i \in 1..N: state[i].color \in NonFadedColor
  /\ \A i \in 1..N: state[i].cnt = 0
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

(* --------------------------------------------------------------------- *)
(*  Actions                                                              *)
(* --------------------------------------------------------------------- *)

Enter ==
  \E c \in 1..N:
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ state[c].color # Faded
    /\ mall' = c
    /\ state' = state
    /\ total' = total

FadeOut ==
  \E c \in 1..N:
    /\ mall = MeetingPlaceEmpty
    /\ total >= M
    /\ state[c].color # Faded
    /\ mall' = MeetingPlaceEmpty
    /\ state' = [state EXCEPT ![c].color = Faded]
    /\ total' = total

MeetAndMutate ==
  \E c \in 1..N:
    LET w == mall IN
    /\ w # MeetingPlaceEmpty
    /\ total < M
    /\ c # w
    /\ state[c].color # Faded
    /\ state[w].color # Faded
    LET newCol == Complement(state[c].color, state[w].color) IN
      /\ mall' = MeetingPlaceEmpty
      /\ total' = total + 1
      /\ state' = [state EXCEPT
                     ![c] = [color |-> newCol, cnt |-> state[c].cnt + 1],
                     ![w] = [color |-> newCol, cnt |-> state[w].cnt + 1]]

Next == Enter \/ FadeOut \/ MeetAndMutate

(* --------------------------------------------------------------------- *)
(*  Specification                                                        *)
(* --------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<state, mall, total>>

(* --------------------------------------------------------------------- *)
(*  Invariants                                                           *)
(* --------------------------------------------------------------------- *)

TypeOK ==
  /\ state \in [1..N -> [color : Color, cnt : Nat]]
  /\ mall \in (MeetingPlaceEmpty \cup 1..N)
  /\ total \in Nat

SumMet ==
  (total = M) => (Sum({state[i].cnt : i \in 1..N}) = 2 * M)

====