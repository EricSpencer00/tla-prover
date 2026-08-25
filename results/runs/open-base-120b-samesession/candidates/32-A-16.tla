---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Colors
\* ----------------------------------------------------------------------
CONSTANTS Blue, Red, Yellow

ColorSet == {Blue, Red, Yellow, Faded}
PrimaryColors == {Blue, Red, Yellow}

\* ----------------------------------------------------------------------
\* Complement rule
\* ----------------------------------------------------------------------
Compl(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE
    CHOOSE c \in PrimaryColors :
      c \notin {c1, c2}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES c, mall, total

\* c : [1..N -> [color : ColorSet, cnt : Nat]]
\* mall : either MeetingPlaceEmpty or an identifier 1..N
\* total : Nat  (global meeting counter)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ c \in [1..N -> [color : PrimaryColors, cnt : Nat]]
  /\ \A i \in 1..N: c[i].cnt = 0
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in 1..N :
        /\ c[i].color # Faded
        /\ mall' = i
        /\ UNCHANGED <<c, total>>
        /\ c' = c

Fade ==
  /\ mall = MeetingPlaceEmpty
  /\ total = M
  /\ \E i \in 1..N :
        /\ c[i].color # Faded
        /\ c' = [c EXCEPT ![i].color = Faded]
        /\ UNCHANGED <<mall, total>>

Meet ==
  /\ mall # MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in 1..N :
        /\ i # mall
        /\ c[i].color # Faded
        /\ c[mall].color # Faded
        /\ LET newcol == Compl(c[i].color, c[mall].color) IN
            /\ c' = [c EXCEPT
                      ![i].color = newcol,
                      ![i].cnt   = @ + 1,
                      ![mall].color = newcol,
                      ![mall].cnt   = @ + 1]
        /\ total' = total + 1
        /\ mall' = MeetingPlaceEmpty

Next == 
  \/ Enter
  \/ Fade
  \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<c, mall, total>>

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ c \in [1..N -> [color : ColorSet, cnt : Nat]]
  /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
  /\ total \in Nat
  /\ total <= M
  /\ \A i \in 1..N : c[i].color \in ColorSet
  /\ \A i \in 1..N : c[i].cnt \in Nat

\* ----------------------------------------------------------------------
\* Safety property: sum of individual meeting counts
\* ----------------------------------------------------------------------
SumMet ==
  (total = M) => (<<>> = <<>> /\ 
    ( \* the sum of all cnt fields equals 2*M *)
    ( \A i \in 1..N : TRUE ) /\ 
    ( \* using finite set sum *)
    ( \* Sum over the set of counts *)
    ( \* Note: Sum is defined in Sequences as Sum over a set of Nat *)
    ( \* we use the built‑in operator \+ over a set via CHOOSE? Instead we use
        \* the standard definition *)
    ( \* The expression below computes the sum *)
    ( \* Convert to a sequence of counts *)
    ( \* Then apply the built‑in Sum *)
    ( \* This is a standard idiom in TLA+ *)
    ( \* Let counts be the set {c[i].cnt : i \in 1..N}
    ( \* and then Sum(counts) *)
    ( \* )
    ( \* )
  ) 
  /\ Sum({c[i].cnt : i \in 1..N}) = 2 * M)

\* ----------------------------------------------------------------------
\* Theorem statement for TLC configuration (optional)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []SumMet

====