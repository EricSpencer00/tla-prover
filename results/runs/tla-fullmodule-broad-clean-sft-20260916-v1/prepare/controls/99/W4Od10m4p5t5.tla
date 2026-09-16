---- MODULE W4Od10m4p5t5 ----
EXTENDS Integers, Sequences

Blocks == {"b1", "b2"}
NONE == "none"
MaxQ == 2

VARIABLES queue, inService, grantCount, occupied, beat

vars == <<queue, inService, grantCount, occupied, beat>>

InQueue(b) == \E k \in 1..Len(queue) : queue[k] = b

TypeOK ==
    /\ queue \in Seq(Blocks)
    /\ inService \in Blocks \cup {NONE}
    /\ grantCount \in [Blocks -> 0..2]
    /\ occupied \in [Blocks -> BOOLEAN]
    /\ beat \in BOOLEAN

Init ==
    /\ queue = <<>>
    /\ inService = NONE
    /\ grantCount = [b \in Blocks |-> 0]
    /\ occupied = [b \in Blocks |-> FALSE]
    /\ beat = FALSE

Request(b) ==
    /\ Len(queue) < MaxQ
    /\ grantCount[b] = 0
    /\ ~ occupied[b]
    /\ ~ InQueue(b)
    /\ inService # b
    /\ queue' = Append(queue, b)
    /\ UNCHANGED <<inService, grantCount, occupied, beat>>

Take ==
    /\ inService = NONE
    /\ Len(queue) > 0
    /\ inService' = Head(queue)
    /\ queue' = Tail(queue)
    /\ UNCHANGED <<grantCount, occupied, beat>>

Grant ==
    /\ inService # NONE
    /\ grantCount[inService] = 0
    /\ ~ occupied[inService]
    /\ grantCount' = [grantCount EXCEPT ![inService] = 1]
    /\ occupied' = [occupied EXCEPT ![inService] = TRUE]
    /\ inService' = NONE
    /\ UNCHANGED <<queue, beat>>

Clear(b) ==
    /\ occupied[b]
    /\ occupied' = [occupied EXCEPT ![b] = FALSE]
    /\ UNCHANGED <<queue, inService, grantCount, beat>>

AdminGrant(b) ==
    /\ grantCount[b] = 0
    /\ ~ occupied[b]
    /\ grantCount' = [grantCount EXCEPT ![b] = 1]
    /\ occupied' = [occupied EXCEPT ![b] = TRUE]
    /\ UNCHANGED <<queue, inService, beat>>

Beat ==
    /\ beat' = ~ beat
    /\ UNCHANGED <<queue, inService, grantCount, occupied>>

Next ==
    \/ \E b \in Blocks : Request(b)
    \/ Take
    \/ Grant
    \/ \E b \in Blocks : Clear(b)
    \/ \E b \in Blocks : AdminGrant(b)
    \/ Beat

Spec == Init /\ [][Next]_vars

AtMostOnceGrant == \A b \in Blocks : grantCount[b] <= 1

====