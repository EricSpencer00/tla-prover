---------------------------- MODULE W4Od8m8p5t2 ----------------------------
EXTENDS Naturals, Sequences
CONSTANTS Courses, Students, Total
VARIABLES coarse, fine, log, pool

None == "none"
Instances == {"A", "B"}
Range(s) == {s[i] : i \in DOMAIN s}

TypeOK ==
    /\ coarse \in Instances \cup {None}
    /\ fine \in [Courses -> Instances \cup {None}]
    /\ log \in Seq(Students)
    /\ pool \in 0..Total

Init ==
    /\ coarse = None
    /\ fine = [k \in Courses |-> None]
    /\ log = << >>
    /\ pool = Total

AcquireCoarse(i) ==
    /\ coarse = None
    /\ coarse' = i
    /\ UNCHANGED <<fine, log, pool>>

ReleaseCoarse(i) ==
    /\ coarse = i
    /\ coarse' = None
    /\ UNCHANGED <<fine, log, pool>>

AcquireFine(i, k) ==
    /\ coarse = i
    /\ fine[k] = None
    /\ fine' = [fine EXCEPT ![k] = i]
    /\ UNCHANGED <<coarse, log, pool>>

Enroll(i, k, s) ==
    /\ fine[k] = i
    /\ pool >= 1
    /\ s \notin Range(log)
    /\ log' = Append(log, s)
    /\ pool' = pool - 1
    /\ UNCHANGED <<coarse, fine>>

ReleaseFine(i, k) ==
    /\ fine[k] = i
    /\ fine' = [fine EXCEPT ![k] = None]
    /\ UNCHANGED <<coarse, log, pool>>

Refill ==
    /\ pool < Total
    /\ pool' = pool + 1
    /\ UNCHANGED <<coarse, fine, log>>

Next ==
    \/ \E i \in Instances : AcquireCoarse(i)
    \/ \E i \in Instances : ReleaseCoarse(i)
    \/ \E i \in Instances, k \in Courses : AcquireFine(i, k)
    \/ \E i \in Instances, k \in Courses, s \in Students : Enroll(i, k, s)
    \/ \E i \in Instances, k \in Courses : ReleaseFine(i, k)
    \/ Refill

Spec == Init /\ [][Next]_<<coarse, fine, log, pool>>

NoDoubleEnroll == \A a, b \in DOMAIN log : log[a] = log[b] => a = b
=============================================================================