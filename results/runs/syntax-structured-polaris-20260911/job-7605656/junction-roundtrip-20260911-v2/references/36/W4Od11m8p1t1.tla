---- MODULE W4Od11m8p1t1 ----
EXTENDS Integers, FiniteSets

Writers == {"w1", "w2"}
Fields == {"fa", "fb"}
NONE == "none"

Fld == [w1 |-> "fa", w2 |-> "fb"]

VARIABLES coarse, fine, record, buf, done

vars == <<coarse, fine, record, buf, done>>

Init ==
    ( (coarse = NONE)
     /\  (fine = NONE)
     /\  (record = {})
     /\  (buf = [w \in Writers |-> {}])
     /\  (done = {}))

\* Coarse spooler lock (acquired first).
AcqCoarse(w) ==
    ( (coarse = NONE)
     /\  (coarse' = w)
     /\  (UNCHANGED <<fine, record, buf, done>>))

\* Fine record lock (acquired only while holding coarse); acquiring it snapshots
\* the current record into the writer's private buffer.
AcqFine(w) ==
    ( (coarse = w)
     /\  (fine = NONE)
     /\  (fine' = w)
     /\  (buf' = [buf EXCEPT ![w] = record])
     /\  (UNCHANGED <<coarse, record, done>>))

\* The lock holder folds its own field into its buffered copy.
AddOwn(w) ==
    ( (fine = w)
     /\  (buf' = [buf EXCEPT ![w] = buf[w] \cup {Fld[w]}])
     /\  (UNCHANGED <<coarse, fine, record, done>>))

\* Write the buffer back to the shared record and release the fine lock. Writes
\* from different writers may be applied in any order, but the fine lock
\* serializes each read-modify-write so none is lost.
Commit(w) ==
    ( (fine = w)
     /\  (Fld[w] \in buf[w])
     /\  (record' = buf[w])
     /\  (done' = done \cup {w})
     /\  (fine' = NONE)
     /\  (UNCHANGED <<coarse, buf>>))

RelCoarse(w) ==
    ( (coarse = w)
     /\  (fine # w)
     /\  (coarse' = NONE)
     /\  (UNCHANGED <<fine, record, buf, done>>))

Next ==
    ( (\E w \in Writers : AcqCoarse(w))
     \/  (\E w \in Writers : AcqFine(w))
     \/  (\E w \in Writers : AddOwn(w))
     \/  (\E w \in Writers : Commit(w))
     \/  (\E w \in Writers : RelCoarse(w)))

Spec == Init /\ [][Next]_vars

TypeOK ==
    ( (coarse \in Writers \cup {NONE})
     /\  (fine \in Writers \cup {NONE})
     /\  (record \subseteq Fields)
     /\  (buf \in [Writers -> SUBSET Fields])
     /\  (done \subseteq Writers))

\* No lost updates: once a writer has committed its field to the shared record,
\* that field is never dropped by a later writer's read-modify-write.
NoLostUpdate ==
    \A w \in done : Fld[w] \in record

====