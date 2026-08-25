---- MODULE Chameneos ----
EXTENDS Naturals, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty
CONSTANTS Blue, Red, Yellow

(* ------------------------------------------------------------------- *)
(*   State variables                                                  *)
(* ------------------------------------------------------------------- *)
VARIABLES state, mall, total

(* ------------------------------------------------------------------- *)
(*   Helper definitions                                               *)
(* ------------------------------------------------------------------- *)
Colors == {Blue, Red, Yellow, Faded}

Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE
        CASE /\ (c1 = Blue /\ c2 = Red) \/ (c1 = Red /\ c2 = Blue)    -> Yellow
             [] /\ (c1 = Blue /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Blue) -> Red
             [] /\ (c1 = Red /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Red) -> Blue
             [] OTHER                                                     -> Faded \* impossible case

(* ------------------------------------------------------------------- *)
(*   Initial state                                                    *)
(* ------------------------------------------------------------------- *)
Init ==
    /\ state = [c \in 1..N |-> [color |-> CHOOSE col \in {Blue, Red, Yellow} : TRUE,
                                cnt   |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

(* ------------------------------------------------------------------- *)
(*   Actions                                                          *)
(* ------------------------------------------------------------------- *)

Enter ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ \E c \in 1..N :
          /\ state[c].color # Faded
          /\ mall' = c
          /\ UNCHANGED <<state, total>>

FadeOut ==
    /\ mall = MeetingPlaceEmpty
    /\ total >= M
    /\ \E c \in 1..N :
          /\ state[c].color # Faded
          /\ state' = [state EXCEPT ![c].color = Faded]
          /\ UNCHANGED <<mall, total>>

Meet ==
    /\ mall # MeetingPlaceEmpty
    /\ total < M
    /\ \E c2 \in 1..N :
          /\ c2 # mall
          /\ state[c2].color # Faded
          /\ state[mall].color # Faded
          /\ LET newCol == Complement(state[mall].color, state[c2].color) IN
                /\ state' = [state EXCEPT
                               ![mall].color = newCol,
                               ![mall].cnt   = @ + 1,
                               ![c2].color   = newCol,
                               ![c2].cnt     = @ + 1]
                /\ mall' = MeetingPlaceEmpty
                /\ total' = total + 1

Next == Enter \/ FadeOut \/ Meet

(* ------------------------------------------------------------------- *)
(*   Specification                                                    *)
(* ------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<state, mall, total>>

(* ------------------------------------------------------------------- *)
(*   Invariants                                                       *)
(* ------------------------------------------------------------------- *)
TypeOK ==
    /\ state \in [1..N -> [color: Colors, cnt: Nat]]
    /\ mall \in (MeetingPlaceEmpty) \cup (1..N)
    /\ total \in Nat

SumMet ==
    total = M => ( Sum({ state[c].cnt : c \in 1..N }) = 2 * M )

====