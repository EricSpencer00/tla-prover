---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES holder, turn, status, live, ticket

vars == <<holder, turn, status, live, ticket>>

TypeOK ==
  /\ holder \in 0..N
  /\ turn \in 0..N
  /\ status \in {"idle", "waiting", "critical"}
  /\ live \in BOOLEAN
  /\ ticket \in 0..MaxNat

Init ==
  /\ holder = 0
  /\ turn = 1
  /\ status = "idle"
  /\ live = TRUE
  /\ ticket = 0

Enter(p) ==
  /\ status = "idle"
  /\ p \notin {holder, turn}
  /\ status' = "waiting"
  /\ ticket' = IF ticket < MaxNat THEN ticket + 1 ELSE ticket
  /\ UNCHANGED <<holder, turn, live>>

PassToken(p) ==
  /\ status = "waiting"
  /\ holder = 0
  /\ holder' = p
  /\ turn' = IF p = N THEN 1 ELSE p + 1
  /\ status' = "critical"
  /\ live' = TRUE
  /\ UNCHANGED ticket

Exit(p) ==
  /\ holder = p
  /\ holder' = 0
  /\ status' = "idle"
  /\ UNCHANGED <<turn, live, ticket>>

Crash(p) ==
  /\ holder = p
  /\ live = TRUE
  /\ live' = FALSE
  /\ UNCHANGED <<holder, turn, status, ticket>>

Reclaim(p) ==
  /\ holder = p
  /\ live = FALSE
  /\ holder' = 0
  /\ status' = "idle"
  /\ UNCHANGED <<turn, live, ticket>>

Next ==
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : PassToken(p)
  \/ \E p \in 1..N : Exit(p)
  \/ \E p \in 1..N : Crash(p)
  \/ \E p \in 1..N : Reclaim(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == holder # 0 => status = "critical"
Inv == status \in {"idle", "waiting", "critical"}

====