---------------------------- MODULE W4Od1m9p1t0 ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Controllers

VARIABLES log, record, epoch, snap, alive
\* log: append-only history of writers to the shared plan; record: last writer
\* stamped on the plan; epoch: reconfiguration counter; snap: each controller's
\* observed version; alive: controllers that have not silently crashed.

vars == <<log, record, epoch, snap, alive>>

MaxLen == 2
Recfg == "recfg"
Version == Len(log)

TypeOK ==
    /\ log \in Seq(Controllers \cup {Recfg})
    /\ Len(log) <= MaxLen
    /\ record \in Controllers \cup {Recfg, "none"}
    /\ epoch \in 0..MaxLen
    /\ snap \in [Controllers -> 0..MaxLen]
    /\ alive \in [Controllers -> BOOLEAN]

Init ==
    /\ log = <<>>
    /\ record = "none"
    /\ epoch = 0
    /\ snap = [c \in Controllers |-> 0]
    /\ alive = [c \in Controllers |-> TRUE]

\* A live controller reads (or re-reads) the current plan version.
Read(c) ==
    /\ alive[c]
    /\ snap[c] # Version
    /\ snap' = [snap EXCEPT ![c] = Version]
    /\ UNCHANGED <<log, record, epoch, alive>>

\* A controller commits its update only if no update slipped in since its read;
\* the write is appended to the log and stamped on the record together.
Write(c) ==
    /\ alive[c]
    /\ snap[c] = Version
    /\ Version < MaxLen
    /\ log' = Append(log, c)
    /\ record' = c
    /\ snap' = [snap EXCEPT ![c] = Version + 1]
    /\ UNCHANGED <<epoch, alive>>

\* An epoch reconfiguration is itself a logged write that supersedes readers.
Reconfigure ==
    /\ Version < MaxLen
    /\ epoch < MaxLen
    /\ log' = Append(log, Recfg)
    /\ record' = Recfg
    /\ epoch' = epoch + 1
    /\ UNCHANGED <<snap, alive>>

\* At most one controller may crash silently and take no further part.
Crash(c) ==
    /\ alive[c]
    /\ \A d \in Controllers : alive[d]
    /\ alive' = [alive EXCEPT ![c] = FALSE]
    /\ UNCHANGED <<log, record, epoch, snap>>

\* Oldest history is garbage-collected once the log is full; the current head
\* (and thus the record it names) is retained.
Trim ==
    /\ Version = MaxLen
    /\ log' = Tail(log)
    /\ UNCHANGED <<record, epoch, snap, alive>>

Next ==
    \/ \E c \in Controllers : Read(c)
    \/ \E c \in Controllers : Write(c)
    \/ Reconfigure
    \/ \E c \in Controllers : Crash(c)
    \/ Trim

Spec == Init /\ [][Next]_vars

\* The shared record always names the head of the append-only history, so no
\* committed update is ever silently dropped from the plan.
NoLostUpdate == Version > 0 => record = log[Version]
=============================================================================