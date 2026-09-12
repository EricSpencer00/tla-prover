---- MODULE W4Od3m0p0t0 ----
EXTENDS Integers

Banks == {"b1", "b2", "b3"}
NONE == "none"

VARIABLES lock, status, snap, ledger
vars == <<lock, status, snap, ledger>>

Init ==
    ( (lock = NONE)
     /\  (status = [b \in Banks |-> "idle"])
     /\  (snap = [b \in Banks |-> NONE])
     /\  (ledger = NONE))

Read(b) ==
    ( (status[b] = "idle")
     /\  (status' = [status EXCEPT ![b] = "trying"])
     /\  (snap' = [snap EXCEPT ![b] = lock])
     /\  (UNCHANGED <<lock, ledger>>))

Acquire(b) ==
    ( (status[b] = "trying")
     /\  (snap[b] = NONE)
     /\  (lock = NONE)
     /\  (lock' = b)
     /\  (status' = [status EXCEPT ![b] = "cs"])
     /\  (UNCHANGED <<snap, ledger>>))

Retry(b) ==
    ( (status[b] = "trying")
     /\  (snap[b] # lock)
     /\  (snap' = [snap EXCEPT ![b] = lock])
     /\  (UNCHANGED <<lock, status, ledger>>))

Exit(b) ==
    ( (status[b] = "cs")
     /\  (lock = b)
     /\  (lock' = NONE)
     /\  (status' = [status EXCEPT ![b] = "idle"])
     /\  (ledger' = b)
     /\  (UNCHANGED snap))

Crash(b) ==
    ( (status[b] # "crashed")
     /\  (status' = [status EXCEPT ![b] = "crashed"])
     /\  (UNCHANGED <<lock, snap, ledger>>))

Recover(b) ==
    ( (status[b] = "crashed")
     /\  (status' = [status EXCEPT ![b] = "idle"])
     /\  (lock' = IF lock = b THEN NONE ELSE lock)
     /\  (snap' = [snap EXCEPT ![b] = NONE])
     /\  (UNCHANGED ledger))

Next ==
    CHOOSE b: (Read(b) \/ Acquire(b) \/ Retry(b) \/ Exit(b) \/ Crash(b) \/ Recover(b))

MutEx ==
    ( (lock = NONE) \/ (EXISTS  (b \in Banks :> (lock = b)))
     /\forall b, b1, b2 \in Banks: (b1 \neq b2) => (lock = b1) => (lock \neq b2))

Spec ==
    Init /\ [][Next]_vars /\ MutEx

====