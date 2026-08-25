---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANT N, M, Faded, MeetingPlaceEmpty

VARIABLES state, mall, total

(* ------------------------------------------------------------------- *)
PrimaryColors == {"blue", "red", "yellow"}

(* Complement rule: same color stays, different colors become the third *)
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE CHOOSE c \in PrimaryColors : c # c1 /\ c # c2

(* ------------------------------------------------------------------- *)
Init ==
  /\ state = [i \in 1..N |-> [color |-> CHOOSE c \in PrimaryColors : TRUE,
                              meetCnt |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

(* A non‑faded creature enters an empty meeting place while meetings remain *)
Enter ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ ∃ i \in 1..N :
        /\ state[i].color # Faded
        /\ mall' = i
        /\ UNCHANGED <<state, total>>

(* When the meeting limit is reached, a creature trying to enter fades out *)
Fade ==
  /\ mall = MeetingPlaceEmpty
  /\ total = M
  /\ ∃ i \in 1..N :
        /\ state[i].color # Faded
        /\ state' = [state EXCEPT ![i].color = Faded]
        /\ UNCHANGED <<mall, total>>

(* Two different non‑faded creatures meet and mutate their colors *)
Meet ==
  /\ total < M
  /\ ∃ i, j \in 1..N :
        /\ i # j
        /\ mall = j
        /\ state[i].color # Faded
        /\ state[j].color # Faded
        /\ LET newc == Complement(state[i].color, state[j].color) IN
              /\ state' = [state EXCEPT
                            ![i] = [color |-> newc,
                                    meetCnt |-> state[i].meetCnt + 1],
                            ![j] = [color |-> newc,
                                    meetCnt |-> state[j].meetCnt + 1]]
              /\ mall' = MeetingPlaceEmpty
              /\ total' = total + 1

Next == Enter \/ Fade \/ Meet

Spec == Init /\ [][Next]_<<state, mall, total>>

(* ------------------------------------------------------------------- *)
TypeOK ==
  /\ state \in [1..N -> [color : PrimaryColors \cup {Faded},
                         meetCnt : Nat]]
  /\ mall \in {MeetingPlaceEmpty} \cup 1..N
  /\ total \in Nat
  /\ total <= M

SumMet ==
  total = M => (Sum({i \in 1..N : state[i].meetCnt}) = 2 * M)

====