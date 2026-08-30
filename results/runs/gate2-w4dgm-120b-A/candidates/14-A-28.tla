---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

AllF == (1..N)

VARIABLES want, inCS, snap, turn, readv, snaps

vars == <<want, inCS, snap, turn, readv, snaps>>

Init ==
  /\ want = [p \in AllF |-> FALSE]
  /\ inCS = [p \in AllF |-> FALSE]
  /\ snap = [p \in AllF |-> 0]
  /\ turn = 0
  /\ readv = [p \in AllF |-> 0]
  /\ snaps = 0

Begin(p) ==
  /\ ~want[p]
  /\ ~inCS[p]
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<inCS, snap, turn, readv, snaps>>

Read(p) ==
  /\ want[p]
  /\ ~inCS[p]
  /\ readv' = [readv EXCEPT ![p] = turn]
  /\ UNCHANGED <<want, inCS, snap, turn, snaps>>

TryEnter(p) ==
  /\ want[p]
  /\ ~inCS[p]
  /\ readv[p] = turn
  /\ turn < MaxNat
  /\ turn' = turn + 1
  /\ snap' = [snap EXCEPT ![p] = turn]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ want' = [want EXCEPT ![p] = FALSE]
  /\ snaps' = IF snaps < MaxNat THEN snaps + 1 ELSE snaps
  /\ UNCHANGED readv

Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<want, snap, turn, readv, snaps>>

Next ==
  \/ \E p \in AllF : Begin(p) \/ Read(p) \/ TryEnter(p) \/ Exit(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ want \in [AllF -> BOOLEAN]
  /\ inCS \in [AllF -> BOOLEAN]
  /\ snap \in [AllF -> (0..MaxNat)]
  /\ turn \in 0..MaxNat
  /\ readv \in [AllF -> 0..MaxNat]
  /\ snaps \in 0..MaxNat

MutualExclusion ==
  \A p \in AllF : inCS[p] => (\A q \in AllF : q # p => ~inCS[q])

Inv ==
  \A p \in AllF : inCS[p] => (snap[p] < turn /\ turn <= snap[p] + (MaxNat \div 2))

StateConstraint == \A p \in AllF : snap[p] < MaxNat

====