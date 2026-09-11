---- MODULE W4Od8m6p0t3 ----
EXTENDS Integers, FiniteSets

Students == {"a", "b"}
NONE == "none"
Dur == 2
MaxT == 6

VARIABLES now, holder, expiry, editing

vars == <<now, holder, expiry, editing>>

Valid == (holder # NONE) /\ (now < expiry)

Init ==
    ( (now     = 0)
     /\  (holder  = NONE)
     /\  (expiry  = 0)
     /\  (editing = {}))

Acquire(s) ==
    ( (editing = {})
     /\  ((holder = NONE \/ now >= expiry))
     /\  (holder'  = s)
     /\  (expiry'  = now + Dur)
     /\  (UNCHANGED <<now, editing>>))

Renew(s) ==
    ( (holder = s)
     /\  (now < expiry)
     /\  (expiry' = now + Dur)
     /\  (UNCHANGED <<now, holder, editing>>))

Enter(s) ==
    ( (holder = s)
     /\  (now < expiry)
     /\  (editing = {})
     /\  (editing' = {s})
     /\  (UNCHANGED <<now, holder, expiry>>))

Exit(s) ==
    ( (s \in editing)
     /\  (editing' = editing \ {s})
     /\  (UNCHANGED <<now, holder, expiry>>))

Tick ==
    ( (now < MaxT)
     /\  (now' = now + 1)
     /\  (editing' = IF now + 1 >= expiry THEN {} ELSE editing)
     /\  (UNCHANGED <<holder, expiry>>))

Next ==
    ( (\E s \in Students : Acquire(s))
     \/  (\E s \in Students : Renew(s))
     \/  (\E s \in Students : Enter(s))
     \/  (\E s \in Students : Exit(s))
     \/  (Tick))

Spec == Init /\ [][Next]_vars

TypeOK ==
    ( (now     \in 0..MaxT)
     /\  (holder  \in Students \cup {NONE})
     /\  (expiry  \in 0..(MaxT + Dur))
     /\  (editing \subseteq Students))

LeaseME ==
    \A s \in editing : (holder = s) /\ (now < expiry)

====