---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors

VARIABLES reading, writing, pending

vars == <<reading, writing, pending>>

Request == [kind : {"read", "write"}, proc : 1..NumActors]

TypeOK ==
  /\ reading \subseteq (1..NumActors)
  /\ writing \subseteq (1..NumActors)
  /\ pending \in Seq(Request)

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ pending = <<>>

RequestRead(i) ==
  /\ ~\E k \in DOMAIN pending : pending[k].proc = i /\ pending[k].kind = "read"
  /\ pending' = Append(pending, [kind |-> "read", proc |-> i])
  /\ UNCHANGED <<reading, writing>>

RequestWrite(i) ==
  /\ ~\E k \in DOMAIN pending : pending[k].proc = i /\ pending[k].kind = "write"
  /\ pending' = Append(pending, [kind |-> "write", proc |-> i])
  /\ UNCHANGED <<reading, writing>>

\* First-come-first-served: only the head of the queue is processed, and
\* a writer must wait until the last reader has gone.
GrantRead ==
  /\ pending # <<>>
  /\ writing = {}
  /\ pending[1].kind = "read"
  /\ reading' = reading \cup {pending[1].proc}
  /\ pending' = Tail(pending)
  /\ UNCHANGED writing

GrantWrite ==
  /\ pending # <<>>
  /\ writing = {}
  /\ pending[1].kind = "write"
  /\ reading = {}
  /\ writing' = writing \cup {pending[1].proc}
  /\ pending' = Tail(pending)
  /\ UNCHANGED reading

StopRead(i) ==
  /\ i \in reading
  /\ reading' = reading \ {i}
  /\ UNCHANGED <<writing, pending>>

StopWrite(i) ==
  /\ i \in writing
  /\ writing' = writing \ {i}
  /\ UNCHANGED <<reading, pending>>

Next ==
  \/ \E i \in 1..NumActors : RequestRead(i)
  \/ \E i \in 1..NumActors : RequestWrite(i)
  \/ GrantRead
  \/ GrantWrite
  \/ \E i \in 1..NumActors : StopRead(i)
  \/ \E i \in 1..NumActors : StopWrite(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..NumActors : RequestRead(i))
  /\ WF_vars(\E i \in 1..NumActors : RequestWrite(i))
  /\ WF_vars(GrantRead)
  /\ WF_vars(GrantWrite)
  /\ \A i \in 1..NumActors : WF_vars(StopRead(i))
  /\ \A i \in 1..NumActors : WF_vars(StopWrite(i))

\* Readers and writers are never active at the same time, and at most one
\* writer is ever active.
Safety ==
  /\ (writing # {} => reading = {})
  /\ (reading # {} => writing = {})

\* Every actor gets to read and to write, and no activity lasts forever.
Liveness ==
  /\ \A i \in 1..NumActors :
       /\ <> (i \in reading \/ i \in writing)
       /\ (i \in reading => <> (i \notin reading))
       /\ (i \in writing => <> (i \notin writing))

====