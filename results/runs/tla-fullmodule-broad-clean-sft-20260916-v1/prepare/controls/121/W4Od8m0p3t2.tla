---------------------------- MODULE W4Od8m0p3t2 ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Students, Seats, Cap, Nil

VARIABLES alloc, ver, snap, want, filled

vars == <<alloc, ver, snap, want, filled>>

TypeOK ==
    /\ alloc \subseteq (Students \X Seats)
    /\ ver \in 0..Cap
    /\ snap \in [Students -> (0..Cap) \cup {Nil}]
    /\ want \in [Students -> Seats \cup {Nil}]
    /\ filled \in 0..Cap

Init ==
    /\ alloc = {}
    /\ ver = 0
    /\ snap = [s \in Students |-> Nil]
    /\ want = [s \in Students |-> Nil]
    /\ filled = 0

Read(st) ==
    /\ snap' = [snap EXCEPT ![st] = ver]
    /\ want' = [want EXCEPT ![st] = Nil]
    /\ UNCHANGED <<alloc, ver, filled>>

Choose(st, s) ==
    /\ snap[st] # Nil
    /\ want[st] = Nil
    /\ \A p \in alloc : p[2] # s
    /\ want' = [want EXCEPT ![st] = s]
    /\ UNCHANGED <<alloc, ver, snap, filled>>

Commit(st) ==
    /\ want[st] # Nil
    /\ snap[st] = ver
    /\ filled < Cap
    /\ alloc' = alloc \cup {<<st, want[st]>>}
    /\ ver' = ver + 1
    /\ filled' = filled + 1
    /\ snap' = [snap EXCEPT ![st] = Nil]
    /\ want' = [want EXCEPT ![st] = Nil]

Retry(st) ==
    /\ snap[st] # Nil
    /\ snap[st] # ver
    /\ snap' = [snap EXCEPT ![st] = Nil]
    /\ want' = [want EXCEPT ![st] = Nil]
    /\ UNCHANGED <<alloc, ver, filled>>

Next ==
    \/ \E st \in Students : Read(st)
    \/ \E st \in Students, s \in Seats : Choose(st, s)
    \/ \E st \in Students : Commit(st)
    \/ \E st \in Students : Retry(st)

Spec == Init /\ [][Next]_vars

NoDoubleSeat ==
    \A x \in alloc : \A y \in alloc : (x[2] = y[2]) => (x[1] = y[1])
=============================================================================