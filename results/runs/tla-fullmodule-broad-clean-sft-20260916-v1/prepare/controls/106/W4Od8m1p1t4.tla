---- MODULE W4Od8m1p1t4 ----
EXTENDS Integers, FiniteSets

Registrars == {"r1", "r2", "r3"}
Ids == {"i1", "i2"}
MaxCap == 2

VARIABLES holder, count, applied, acked, cap

vars == <<holder, count, applied, acked, cap>>

NextR(r) == CASE r = "r1" -> "r2"
              [] r = "r2" -> "r3"
              [] r = "r3" -> "r1"

Init ==
    /\ holder = "r1"
    /\ count = 0
    /\ applied = {}
    /\ acked = {}
    /\ cap = 1

Pass(r) ==
    /\ holder = r
    /\ holder' = NextR(r)
    /\ UNCHANGED <<count, applied, acked, cap>>

Write(r, id) ==
    /\ holder = r
    /\ count < cap
    /\ id \notin applied
    /\ count' = count + 1
    /\ applied' = applied \cup {id}
    /\ UNCHANGED <<holder, acked, cap>>

Ack(id) ==
    /\ id \in applied
    /\ id \notin acked
    /\ acked' = acked \cup {id}
    /\ UNCHANGED <<holder, count, applied, cap>>

SetCap(c) ==
    /\ c \in 0..MaxCap
    /\ c # cap
    /\ cap' = c
    /\ UNCHANGED <<holder, count, applied, acked>>

Next ==
    \/ \E r \in Registrars : Pass(r)
    \/ \E r \in Registrars, id \in Ids : Write(r, id)
    \/ \E id \in Ids : Ack(id)
    \/ \E c \in 0..MaxCap : SetCap(c)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ holder \in Registrars
    /\ count \in 0..MaxCap
    /\ applied \subseteq Ids
    /\ acked \subseteq Ids
    /\ cap \in 0..MaxCap

NoLostUpdate ==
    acked \subseteq applied

====