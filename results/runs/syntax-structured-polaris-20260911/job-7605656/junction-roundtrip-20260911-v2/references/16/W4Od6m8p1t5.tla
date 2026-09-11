---- MODULE W4Od6m8p1t5 ----
EXTENDS Integers
CONSTANTS Ctrls, MaxVal
Nobody == "nobody"
VARIABLES coarse, fine, value, active, snap
vars == <<coarse, fine, value, active, snap>>

TypeOK ==
  ( (coarse \in Ctrls \cup {Nobody})
   /\  (fine \in Ctrls \cup {Nobody})
   /\  (value \in 0..MaxVal)
   /\  (active \in Ctrls \cup {Nobody})
   /\  (snap \in -1..MaxVal))

Init ==
  ( (coarse = Nobody)
   /\  (fine = Nobody)
   /\  (value = 0)
   /\  (active = Nobody)
   /\  (snap = -1))

TakeCoarse(c) ==
  ( (coarse = Nobody)
   /\  (coarse' = c)
   /\  (UNCHANGED <<fine, value, active, snap>>))

TakeFine(c) ==
  ( (coarse = c)
   /\  (fine = Nobody)
   /\  (fine' = c)
   /\  (UNCHANGED <<coarse, value, active, snap>>))

ReadSnap(c) ==
  ( (fine = c)
   /\  (active = Nobody)
   /\  (active' = c)
   /\  (snap' = value)
   /\  (UNCHANGED <<coarse, fine, value>>))

Commit(c) ==
  ( (active = c)
   /\  (snap < MaxVal)
   /\  (value' = snap + 1)
   /\  (active' = Nobody)
   /\  (snap' = -1)
   /\  (coarse' = Nobody)
   /\  (fine' = Nobody))

AdminOverride ==
  ( (active = Nobody)
   /\  (value < MaxVal)
   /\  (value' = value + 1)
   /\  (UNCHANGED <<coarse, fine, active, snap>>))

Next ==
  ( (\E c \in Ctrls : TakeCoarse(c))
   \/  (\E c \in Ctrls : TakeFine(c))
   \/  (\E c \in Ctrls : ReadSnap(c))
   \/  (\E c \in Ctrls : Commit(c))
   \/  (AdminOverride))

Spec == Init /\ [][Next]_vars

NoLostUpdate == (active = Nobody) \/ (snap = value)
====