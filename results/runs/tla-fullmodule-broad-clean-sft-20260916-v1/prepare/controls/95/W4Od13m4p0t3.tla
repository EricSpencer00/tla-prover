---- MODULE W4Od13m4p0t3 ----
EXTENDS Integers

Workers == {"w1", "w2"}
NONE == "none"
Cap == 2
MaxJobs == 3

VARIABLES qlen, total, lock, wstate

vars == <<qlen, total, lock, wstate>>

Init ==
    /\ qlen = 0
    /\ total = 0
    /\ lock = NONE
    /\ wstate = [w \in Workers |-> "idle"]

Enqueue ==
    /\ qlen < Cap
    /\ total < MaxJobs
    /\ qlen' = qlen + 1
    /\ total' = total + 1
    /\ UNCHANGED <<lock, wstate>>

Take(w) ==
    /\ wstate[w] = "idle"
    /\ qlen > 0
    /\ qlen' = qlen - 1
    /\ wstate' = [wstate EXCEPT ![w] = "hasjob"]
    /\ UNCHANGED <<total, lock>>

Enter(w) ==
    /\ wstate[w] = "hasjob"
    /\ lock = NONE
    /\ lock' = w
    /\ wstate' = [wstate EXCEPT ![w] = "incs"]
    /\ UNCHANGED <<qlen, total>>

Exit(w) ==
    /\ wstate[w] = "incs"
    /\ lock' = NONE
    /\ wstate' = [wstate EXCEPT ![w] = "idle"]
    /\ UNCHANGED <<qlen, total>>

Idle ==
    /\ total = MaxJobs
    /\ qlen = 0
    /\ \A w \in Workers : wstate[w] = "idle"
    /\ UNCHANGED vars

Next ==
    \/ Enqueue
    \/ \E w \in Workers : Take(w)
    \/ \E w \in Workers : Enter(w)
    \/ \E w \in Workers : Exit(w)
    \/ Idle

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ qlen \in 0..Cap
    /\ total \in 0..MaxJobs
    /\ lock \in Workers \cup {NONE}
    /\ wstate \in [Workers -> {"idle", "hasjob", "incs"}]

MutualExclusion ==
    \A w \in Workers : wstate[w] = "incs" => lock = w

====