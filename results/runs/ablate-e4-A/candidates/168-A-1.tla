---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANT NumActors

VARIABLES Readers, Writers, Queue

Actors == 1..NumActors

ReadMode == "READ"
WriteMode == "WRITE"

RecordType == [proc: Actors, mode: {"READ","WRITE"}]

Init ==
  /\ Readers = {}
  /\ Writers = {}
  /\ Queue   = <<>>

InQueue(p, m) == ∃r ∈ Queue : r.proc = p /\ r.mode = m

RequestRead(p) ==
  /\ p ∈ Actors
  /\ p ∉ Readers
  /\ p ∉ Writers
  /\ ~InQueue(p, ReadMode)
  /\ Queue'   = Append(Queue, [proc |-> p, mode |-> ReadMode])
  /\ Readers' = Readers
  /\ Writers' = Writers

RequestWrite(p) ==
  /\ p ∈ Actors
  /\ p ∉ Readers
  /\ p ∉ Writers
  /\ ~InQueue(p, WriteMode)
  /\ Queue'   = Append(Queue, [proc |-> p, mode |-> WriteMode])
  /\ Readers' = Readers
  /\ Writers' = Writers

BeginRead ==
  /\ Queue # <<>>
  /\ Queue[1].mode = ReadMode
  /\ Writers = {}
  /\ Queue'   = Tail(Queue)
  /\ Readers' = Readers ∪ {Queue[1].proc}
  /\ Writers' = Writers

BeginWrite ==
  /\ Queue # <<>>
  /\ Queue[1].mode = WriteMode
  /\ Readers = {}
  /\ Queue'   = Tail(Queue)
  /\ Writers' = Writers ∪ {Queue[1].proc}
  /\ Readers' = Readers

Stop(p) ==
  /\ p ∈ Actors
  /\ (p ∈ Readers ∨ p ∈ Writers)
  /\ Queue'   = Queue
  /\ Readers' = Readers \ {p}
  /\ Writers' = Writers \ {p}

Next ==
  \E p \in Actors :
      (RequestRead(p) \/ RequestWrite(p) \/ Stop(p))
      \/ BeginRead
      \/ BeginWrite

Spec == Init /\ [][Next]_<<Readers, Writers, Queue>>

TypeOK ==
  /\ Readers \subseteq Actors
  /\ Writers \subseteq Actors
  /\ Readers # Writers
  /\ Queue \in Seq(RecordType)
  /\ \A r \in Queue : r.proc \in Actors /\ r.mode \in {"READ","WRITE"}

Safety ==
  /\ Readers # Writers
  /\ #Writers <= 1

Liveness ==
  \A p \in Actors :
      (◇(p ∈ Readers) /\ ◇(p ∈ Writers))
      /\ □( (p ∈ Readers) => ◇(p ∉ Readers) )
      /\ □( (p ∈ Writers) => ◇(p ∉ Writers) )

====