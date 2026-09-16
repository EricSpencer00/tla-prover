---- MODULE W4Od8m2p5t0 ----
EXTENDS Naturals

Students == {"s1", "s2", "s3"}

VARIABLES prepared, finalized, crashed, beat
vars == << prepared, finalized, crashed, beat >>

TypeOK ==
    /\ prepared \subseteq Students
    /\ finalized \subseteq Students
    /\ crashed \subseteq Students
    /\ beat \in 0..2

Init ==
    /\ prepared = {}
    /\ finalized = {}
    /\ crashed = {}
    /\ beat = 0

Prepare(s) ==
    /\ s \notin prepared
    /\ s \notin finalized
    /\ s \notin crashed
    /\ prepared' = prepared \cup {s}
    /\ UNCHANGED << finalized, crashed, beat >>

Finalize(s) ==
    /\ s \in prepared
    /\ prepared' = prepared \ {s}
    /\ finalized' = finalized \cup {s}
    /\ UNCHANGED << crashed, beat >>

Crash(s) ==
    /\ s \in prepared
    /\ prepared' = prepared \ {s}
    /\ crashed' = crashed \cup {s}
    /\ UNCHANGED << finalized, beat >>

Recover(s) ==
    /\ s \in crashed
    /\ crashed' = crashed \ {s}
    /\ UNCHANGED << prepared, finalized, beat >>

Heartbeat ==
    /\ beat' = (beat + 1) % 3
    /\ UNCHANGED << prepared, finalized, crashed >>

Next ==
    \/ \E s \in Students : Prepare(s)
    \/ \E s \in Students : Finalize(s)
    \/ \E s \in Students : Crash(s)
    \/ \E s \in Students : Recover(s)
    \/ Heartbeat

Spec == Init /\ [][Next]_vars

PreparedNotFinalized == prepared \cap finalized = {}
====