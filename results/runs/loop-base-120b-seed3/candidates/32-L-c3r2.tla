---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N, M, Faded, MeetingPlaceEmpty

VARIABLES col, cnt, mp, total

(* Primary (non‑faded) colors *)
PrimaryColors == {"blue", "red", "yellow"}

(* Full set of colors, including the faded one *)
Color == PrimaryColors \cup {Faded}

(* Complementation rule *)
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c \in PrimaryColors : c # c1 /\ c # c2

(* Initial state *)
Init ==
    /\ col \in [1..N -> PrimaryColors]      \* each creature starts with a primary color
    /\ cnt = [i \in 1..N |-> 0]              \* zero meetings for everybody
    /\ mp = MeetingPlaceEmpty                \* meeting place initially empty
    /\ total = 0

(* A non‑faded creature enters an empty meeting place *)
Enter(i) ==
    /\ i \in 1..N
    /\ mp = MeetingPlaceEmpty
    /\ total < M
    /\ col[i] # Faded
    /\ mp' = i
    /\ UNCHANGED <<col, cnt, total>>

(* When the limit has been reached, a creature that tries to enter fades out *)
Fade(i) ==
    /\ i \in 1..N
    /\ mp = MeetingPlaceEmpty
    /\ total = M
    /\ col[i] # Faded
    /\ col' = [col EXCEPT ![i] = Faded]
    /\ UNCHANGED <<cnt, mp, total>>

(* Two different creatures meet and mutate *)
Meet(i, j) ==
    /\ i \in 1..N
    /\ j \in 1..N
    /\ i # j
    /\ mp = j
    /\ total < M
    /\ col[i] # Faded
    /\ col[j] # Faded
    /\ LET newCol == Complement(col[i], col[j]) IN
         /\ col' = [col EXCEPT ![i] = newCol, ![j] = newCol]
         /\ cnt' = [cnt EXCEPT ![i] = @+1, ![j] = @+1]
         /\ total' = total + 1
         /\ mp' = MeetingPlaceEmpty

Next ==
    \/ \E i \in 1..N: Enter(i)
    \/ \E i \in 1..N: Fade(i)
    \/ \E i \in 1..N, j \in 1..N: Meet(i, j)

Spec ==
    Init /\ [][Next]_<<col, cnt, mp, total>>

(* Type invariant *)
TypeOK ==
    /\ col \in [1..N -> Color]
    /\ cnt \in [1..N -> Nat]
    /\ mp \in (MeetingPlaceEmpty \/ 1..N)
    /\ total \in Nat

(* Safety invariant: when the global counter reaches the limit,
   the sum of individual counts equals twice that limit *)
SumMet ==
    total = M => (Sum({cnt[i] : i \in 1..N}) = 2 * M)

====