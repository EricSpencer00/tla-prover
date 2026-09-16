---------------------------- MODULE W4Od5m1p1t2 ----------------------------
(* Multiplayer game lobby: two matchmaker instances share one roster log,
   serialized by a token ring. Only the token-holding instance may append the
   next update id, and only when its snapshot of the high-water mark still
   matches. Because one token admits a single writer, appended ids stay gapless:
   the set of applied update ids is always exactly 1..high, so no update is lost
   or skipped. *)
EXTENDS Naturals

Nodes == 1..2
MaxV == 3
RingNext(n) == (n % 2) + 1

VARIABLES high, applied, snap, holder, passes

vars == <<high, applied, snap, holder, passes>>

TypeOK ==
    /\ high \in 0..MaxV
    /\ applied \in SUBSET (1..MaxV)
    /\ snap \in 0..MaxV
    /\ holder \in Nodes
    /\ passes \in 0..5

Init ==
    /\ high = 0
    /\ applied = {}
    /\ snap = 0
    /\ holder = 1
    /\ passes = 0

Snapshot(n) ==
    /\ holder = n
    /\ snap' = high
    /\ UNCHANGED <<high, applied, holder, passes>>

Append(n) ==
    /\ holder = n
    /\ snap = high
    /\ high < MaxV
    /\ high' = high + 1
    /\ applied' = applied \cup {high + 1}
    /\ UNCHANGED <<snap, holder, passes>>

PassToken(n) ==
    /\ holder = n
    /\ holder' = RingNext(n)
    /\ passes' = (passes + 1) % 6
    /\ UNCHANGED <<high, applied, snap>>

Compact ==
    /\ high = MaxV
    /\ high' = 0
    /\ applied' = {}
    /\ UNCHANGED <<snap, holder, passes>>

Next ==
    \/ \E n \in Nodes : Snapshot(n)
    \/ \E n \in Nodes : Append(n)
    \/ \E n \in Nodes : PassToken(n)
    \/ Compact

Spec == Init /\ [][Next]_vars

GaplessLog == applied = 1..high
============================================================================