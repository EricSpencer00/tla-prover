---- MODULE W4Od3m0p0t0 ----
CONSTANTS Banks, Ledger, Rebooted, Crashed
VARIABLES snapshot, holder, Lock, Ledger', Rebooted', Crashed'
vars == <<snapshot, holder, Lock, Ledger', Crashed>>

Init == snapshot = [b |-> "free" : b \in Banks] /\ holder = "none" /\ Lock = "none" /\ Ledger = {} /\ Crashed = [b |-> F : b \in Banks]

Next == \/ crash(b) \/ reboot(b) \/ idle(b) \/ compareAndSet(b) \/ post(b)
crush(b) == snapshot' = snapshot \ {b} /\ holder' = "none" /\ Crashed' = [Crashed EXCEPT![b] = T]
reboot(b) == snapshot' = snapshot  \/ snapshot' = [b | -> "free"] /\ holder' =  "none" /\ Rebooted' = [Rebooted EXCEPT![b] = T] 
idle(b) == snapshot' = [snapshot EXCEPT![b] = "free"] /\ holder' = [holder EXCEPT![b] = "none"] 
compareAndSet(b) == snapshot' = [snap |-> snap' : snap \in snapshot \ {b}] /\ holder' = [holder EXcept![b] = "none"] /\ snapshot' = [snapshot EXCEPT ![b] = "held by " \union {b}] /\ Lock' = b
post(b) == snapshot' = snapshot' = [snap |-> b : snap \in snapshot] /\ holder' = b /\ Lock = b /\ Ledger' = Ledger  \cup {b}

MutEx ==
    \A b \in Banks : holder  = "none" => snapshot[b] = "free"
    \A b \in Banks, snap \in "free" \cup "held by " \cup {snap : snap \in snapshot} : snapshot' = [snap |-> snapshot[b]] => snap = snapshot[b]
    \A b \in Banks  : holder  = b => snapshot[b] = snapshot[b]
    \A c \in Banks : snapshot[b]  = snapshot[b] => snapshot[b] = snapshot[b] 
    \A b \in Banks, snap \in snapshot : snapshot[b] = snap => snapshot[b] = snap
    \A b \in Banks: snapshot[b] = "held by" \cup {b} => holder = b
    \A b \in  Banks : snapshot[b] = "held by \cup {b} => holder  = b
    \A b, c \in Banks : snapshot[b]= snapshot[c] => b = c
    \A b \in Bank : snapshot[b] = "free " => snapshot[b] = "free "
    \A b \in Banks   : snapshot[b] = "held  by " \cup {b} => snapshot[b] = "held  " \cup {b}
    \A b \in Banks    : snapshot[b] = "held " \cup {b} => holder   = b
    \A b  \in Banks : snapshot[b]   = snapshot[b]
    \A a, b \in Banks : snapshot[a] = snapshot[b] => a = b
    \A b,c \in Banks : snapshot[b] \cup snapshot[c] => snapshot[b] = snapshot[c]
    \A b \in Bank: snapshot[b] = snapshot[b]
Spec == Init /\ [][Next \* vars]_vars
====