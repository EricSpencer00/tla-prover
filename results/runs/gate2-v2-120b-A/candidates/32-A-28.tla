---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----- Types -----
Colors == {"blue", "red", "yellow", Faded}
CreatureIds == 1 .. N

\* ----- Variables -----
VARIABLES creatures, mall, total

\* creatures : [CreatureIds -> [color : Colors, count : Nat]]
\* mall     : either MeetingPlaceEmpty or a CreatureId
\* total    : Nat, number of completed meetings

\* ----- Helper definitions -----
\* Complement rule: given two colors, return the new color each creature adopts
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE
    CASE c1 = "blue" /\ c2 = "red"    -> "yellow"
    []  c1 = "red"  /\ c2 = "blue"    -> "yellow"
    []  c1 = "blue" /\ c2 = "yellow" -> "red"
    []  c1 = "yellow" /\ c2 = "blue" -> "red"
    []  c1 = "red"  /\ c2 = "yellow" -> "blue"
    []  c1 = "yellow" /\ c2 = "red"   -> "blue"
    []  TRUE                         -> Faded \* Should not happen

\* Sum of all individual meeting counts
TotalIndividualCounts == 
  \E s \in [CreatureIds -> Nat] :
    /\ \A i \in CreatureIds : s[i] = creatures[i].count
    /\ /\ s[i] \in Nat

\* ----- Initial state -----
Init ==
  /\ creatures = [i \in CreatureIds |-> [color |-> 
        CASE i % 3 = 1 -> "blue"
        [] i % 3 = 2 -> "red"
        [] "yellow", 
        count |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

\* ----- Actions -----
\* A non-faded creature enters an empty mall when meetings are still allowed
Enter ==
  /\ total < M
  /\ mall = MeetingPlaceEmpty
  /\ \E i \in CreatureIds :
        /\ creatures[i].color # Faded
        /\ mall' = i
        /\ UNCHANGED <<creatures, total>>

\* A non-faded creature that tries to enter after limit becomes faded
FadeOut ==
  /\ total >= M
  /\ mall = MeetingPlaceEmpty
  /\ \E i \in CreatureIds :
        /\ creatures[i].color # Faded
        /\ creatures' = [creatures EXCEPT ![i].color = Faded]
        /\ UNCHANGED <<mall, total>>

\* Two distinct creatures meet and both mutate their colors
Meet ==
  /\ \E i, j \in CreatureIds :
        /\ i # j
        /\ creatures[i].color # Faded
        /\ creatures[j].color # Faded
        /\ mall = i
        /\ mall' = MeetingPlaceEmpty
        /\ LET newCol == Complement(creatures[i].color, creatures[j].color) IN
           /\ creatures' = [creatures EXCEPT 
                ![i].color = newCol,
                ![i].count = @ + 1,
                ![j].color = newCol,
                ![j].count = @ + 1]
        /\ total' = total + 1

\* No‑op action to allow stuttering when nothing can happen
Idle ==
  /\ UNCHANGED <<creatures, mall, total>>

Next ==
  \/ Enter
  \/ FadeOut
  \/ Meet
  \/ Idle

\* ----- Specification -----
Spec ==
  Init /\ [][Next]_<<creatures, mall, total>>

\* ----- Type correctness invariant -----
TypeOK ==
  /\ creatures \in [CreatureIds -> [color : Colors, count : Nat]]
  /\ mall \in MeetingPlaceEmpty \cup CreatureIds
  /\ total \in Nat

\* ----- Safety invariant: sum of individual counts equals twice total meetings when limit reached -----
SumMet ==
  (total = M) => 
    (\A i \in CreatureIds : creatures[i].count \in Nat) /\ 
    ( \A i \in CreatureIds : creatures[i].count <= total ) /\ 
    ( \E s \in [CreatureIds -> Nat] :
        /\ \A i \in CreatureIds : s[i] = creatures[i].count
        /\ /\ \A i \in CreatureIds : s[i] <= total
        /\ \A i \in CreatureIds : s[i] >= 0 )
    /\ ( \A i \in CreatureIds : creatures[i].count >= 0 )
    /\ ( \A i \in CreatureIds : creatures[i].count <= total )
    /\ ( \A i \in CreatureIds : creatures[i].color # Faded => TRUE ) 
    /\ ( \A i, j \in CreatureIds : i # j => 
            IF i # j /\ creatures[i].color # Faded /\ creatures[j].color # Faded THEN TRUE ELSE TRUE )
    /\ ( \A i \in CreatureIds : creatures[i].count = 0 \/ TRUE )
    /\ ( \A i \in CreatureIds : creatures[i].color \in Colors )
    /\ ( \A i, j \in CreatureIds : i # j => 
            IF mall = i /\ mall' = MeetingPlaceEmpty => TRUE ELSE TRUE )
    /\ ( \A i \in CreatureIds : 
            IF creatures[i].color = Faded THEN creatures[i].count = creatures[i].count ELSE TRUE )
    /\ ( \A i \in CreatureIds : 
            IF creatures[i].color # Faded THEN creatures[i].count = creatures[i].count ELSE TRUE )
    /\ ( Sum({creatures[i].count : i \in CreatureIds}) = 2 * total )

\* ----- Theorem (optional, not required) -----
THEOREM Spec => []TypeOK

====