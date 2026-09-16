---- MODULE W4Od10m0p3t5 ----
EXTENDS Integers

Trains == {"t1", "t2"}
Blocks == {"b1", "b2"}
MaxV == 3

NoAttempt == [blk |-> "none", rv |-> 0]

VARIABLES owner, version, attempt, override

vars == <<owner, version, attempt, override>>

TypeOK ==
    /\ owner \in [Blocks -> Trains \cup {"none"}]
    /\ version \in [Blocks -> 0..MaxV]
    /\ attempt \in [Trains -> [blk : Blocks \cup {"none"}, rv : 0..MaxV]]
    /\ override \in BOOLEAN

Init ==
    /\ owner = [b \in Blocks |-> "none"]
    /\ version = [b \in Blocks |-> 0]
    /\ attempt = [t \in Trains |-> NoAttempt]
    /\ override = FALSE

BeginAttempt(t, b) ==
    /\ attempt[t].blk = "none"
    /\ owner[b] = "none"
    /\ attempt' = [attempt EXCEPT ![t] = [blk |-> b, rv |-> version[b]]]
    /\ UNCHANGED <<owner, version, override>>

CommitAttempt(t) ==
    /\ attempt[t].blk # "none"
    /\ LET b == attempt[t].blk IN
         /\ owner[b] = "none"
         /\ version[b] = attempt[t].rv
         /\ version[b] < MaxV
         /\ owner' = [owner EXCEPT ![b] = t]
         /\ version' = [version EXCEPT ![b] = version[b] + 1]
    /\ attempt' = [attempt EXCEPT ![t] = NoAttempt]
    /\ UNCHANGED override

AbortAttempt(t) ==
    /\ attempt[t].blk # "none"
    /\ attempt' = [attempt EXCEPT ![t] = NoAttempt]
    /\ UNCHANGED <<owner, version, override>>

Release(t, b) ==
    /\ owner[b] = t
    /\ version[b] < MaxV
    /\ owner' = [owner EXCEPT ![b] = "none"]
    /\ version' = [version EXCEPT ![b] = version[b] + 1]
    /\ UNCHANGED <<attempt, override>>

ArmOverride ==
    /\ override = FALSE
    /\ override' = TRUE
    /\ UNCHANGED <<owner, version, attempt>>

DisarmOverride ==
    /\ override = TRUE
    /\ override' = FALSE
    /\ UNCHANGED <<owner, version, attempt>>

AdminForce(t, b) ==
    /\ override = TRUE
    /\ version[b] < MaxV
    /\ owner' = [owner EXCEPT ![b] = t]
    /\ version' = [version EXCEPT ![b] = version[b] + 1]
    /\ UNCHANGED <<attempt, override>>

Next ==
    \/ \E t \in Trains, b \in Blocks : BeginAttempt(t, b)
    \/ \E t \in Trains : CommitAttempt(t)
    \/ \E t \in Trains : AbortAttempt(t)
    \/ \E t \in Trains, b \in Blocks : Release(t, b)
    \/ ArmOverride
    \/ DisarmOverride
    \/ \E t \in Trains, b \in Blocks : AdminForce(t, b)

Spec == Init /\ [][Next]_vars

NoDoubleAlloc ==
    \A t \in Trains :
        (attempt[t].blk # "none" /\ owner[attempt[t].blk] # "none")
          => version[attempt[t].blk] # attempt[t].rv
====