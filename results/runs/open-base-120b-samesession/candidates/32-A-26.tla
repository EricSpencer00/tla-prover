---- MODULE Chameneos ----
EXTENDS Naturals, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

(*--algorithm placeholder for constants only--*)

(* Colors *)
Blue   == "blue"
Red    == "red"
Yellow == "yellow"

Colors == {Blue, Red, Yellow, Faded}
CreatureIds == 1 .. N

(* State variables *)
VARIABLES creatures, mall, total

(* Complement rule: if same color keep it, otherwise switch to the third color *)
Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CHOOSE col \in {Blue, Red, Yellow} : col # c1 /\ col # c2

(* Initial state *)
Init ==
  /\ creatures = [c \in CreatureIds |-> [color |-> CHOOSE col \in {Blue, Red, Yellow} : TRUE,
                                          count |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

(* Action: a non‑faded creature enters an empty meeting place before the limit is reached *)
Enter(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ c \in CreatureIds
  /\ creatures[c].color # Faded
  /\ mall' = c
  /\ UNCHANGED <<creatures, total>>

(* Action: after the limit, a creature that tries to enter fades out *)
Fade(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ total = M
  /\ c \in CreatureIds
  /\ creatures[c].color # Faded
  /\ creatures' = [creatures EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<mall, total>>

(* Action: two different non‑faded creatures meet and mutate their colors *)
Meet(c2) ==
  /\ mall # MeetingPlaceEmpty               \* there is a waiting creature c1 = mall
  /\ total < M
  /\ c2 \in CreatureIds
  /\ c2 # mall
  /\ creatures[mall].color # Faded
  /\ creatures[c2].color # Faded
  /\ LET newcol == Complement(creatures[mall].color, creatures[c2].color) IN
        /\ creatures' = [creatures EXCEPT
                           ![mall].color = newcol,
                           ![mall].count = @ + 1,
                           ![c2].color   = newcol,
                           ![c2].count   = @ + 1]
        /\ total' = total + 1
        /\ mall' = MeetingPlaceEmpty

(* Next-state relation *)
Next ==
  \/ \E c \in CreatureIds : Enter(c)
  \/ \E c \in CreatureIds : Fade(c)
  \/ \E c2 \in CreatureIds : Meet(c2)
  \/ UNCHANGED <<creatures, mall, total>>

(* Specification *)
Spec == Init /\ [][Next]_<<creatures, mall, total>>

(* Type correctness invariant *)
TypeOK ==
  /\ creatures \in [CreatureIds -> [color : Colors, count : Nat]]
  /\ mall \in CreatureIds \cup {MeetingPlaceEmpty}
  /\ total \in Nat
  /\ total <= M

(* Safety property: when the global counter reaches M, the sum of individual counts equals 2*M *)
SumCounts == Sum({c \in CreatureIds : creatures[c].count})
SumMet ==
  total = M => SumCounts = 2 * M

====