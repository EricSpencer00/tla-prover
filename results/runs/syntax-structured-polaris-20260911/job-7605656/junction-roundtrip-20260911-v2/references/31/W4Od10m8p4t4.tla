---- MODULE W4Od10m8p4t4 ----
EXTENDS Integers, FiniteSets

Regions == {"r1", "r2"}
Seg == {"s1", "s2", "s3", "s4"}
Trains == {"t1", "t2"}
NONE == "none"
MaxCap == 2

RegionOf(s) == IF s \in {"s1", "s2"} THEN "r1" ELSE "r2"

VARIABLES intent, coarseOf, seg, cap

vars == <<intent, coarseOf, seg, cap>>

Occ(r) == Cardinality({s \in Seg : RegionOf(s) = r /\ seg[s] # NONE})

Init ==
    ( (intent = [t \in Trains |-> NONE])
     /\  (coarseOf = [t \in Trains |-> NONE])
     /\  (seg = [s \in Seg |-> NONE])
     /\  (cap = [r \in Regions |-> 1]))

Request(t, r) ==
    ( (coarseOf[t] = NONE)
     /\  (intent[t] = NONE)
     /\  (intent' = [intent EXCEPT ![t] = r])
     /\  (UNCHANGED <<coarseOf, seg, cap>>))

AcquireCoarse(t) ==
    ( (intent[t] # NONE)
     /\  (coarseOf[t] = NONE)
     /\  (coarseOf' = [coarseOf EXCEPT ![t] = intent[t]])
     /\  (intent' = [intent EXCEPT ![t] = NONE])
     /\  (UNCHANGED <<seg, cap>>))

AcquireFine(t, s) ==
    ( (coarseOf[t] = RegionOf(s))
     /\  (seg[s] = NONE)
     /\  (Occ(RegionOf(s)) < cap[RegionOf(s)])
     /\  (seg' = [seg EXCEPT ![s] = t])
     /\  (UNCHANGED <<intent, coarseOf, cap>>))

ReleaseFine(t, s) ==
    ( (seg[s] = t)
     /\  (seg' = [seg EXCEPT ![s] = NONE])
     /\  (UNCHANGED <<intent, coarseOf, cap>>))

ReleaseCoarse(t) ==
    ( (coarseOf[t] # NONE)
     /\  (\A s \in Seg : seg[s] # t)
     /\  (coarseOf' = [coarseOf EXCEPT ![t] = NONE])
     /\  (UNCHANGED <<intent, seg, cap>>))

ChangeCap(r, c) ==
    ( (c \in 1..MaxCap)
     /\  (c # cap[r])
     /\  (c >= Occ(r))
     /\  (cap' = [cap EXCEPT ![r] = c])
     /\  (UNCHANGED <<intent, coarseOf, seg>>))

Next ==
    ( (\E t \in Trains, r \in Regions : Request(t, r))
     \/  (\E t \in Trains : AcquireCoarse(t))
     \/  (\E t \in Trains, s \in Seg : AcquireFine(t, s))
     \/  (\E t \in Trains, s \in Seg : ReleaseFine(t, s))
     \/  (\E t \in Trains : ReleaseCoarse(t))
     \/  (\E r \in Regions, c \in 1..MaxCap : ChangeCap(r, c)))

Spec == Init /\ [][Next]_vars

TypeOK ==
    ( (intent \in [Trains -> Regions \cup {NONE}])
     /\  (coarseOf \in [Trains -> Regions \cup {NONE}])
     /\  (seg \in [Seg -> Trains \cup {NONE}])
     /\  (cap \in [Regions -> 1..MaxCap]))

WithinCapacity ==
    \A r \in Regions : Occ(r) <= cap[r]

====