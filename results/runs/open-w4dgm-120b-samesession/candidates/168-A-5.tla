---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
  /\ reading \subseteq 1..NumActors
  /\ writing \subseteq 1..NumActors
  /\ queue \in Seq([pid: 1..NumActors, mode: {"r", "w"}])

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = <<>>

Request(mode, p) ==
  /\ mode \in {"r", "w"}
  /\ ~ \E i \in 1..Len(queue) : queue[i].pid = p
  /\ queue' = Append(queue, [pid |-> p, mode |-> mode])
  /\ UNCHANGED <<reading, writing>>

BeginAccess ==
  /\ Len(queue) > 0
  /\ writing = {}
  /\ LET m == Head(queue) IN
       /\ queue' = Tail(queue)
       /\ IF m.mode = "r" THEN reading' = reading \cup {m.pid} ELSE reading' = reading
       /\ IF m.mode = "w" /\ reading = {} THEN writing' = writing \cup {m.pid} ELSE writing' = writing
  /\ UNCHANGED <<>>

StopActivity(p) ==
  /\ p \in reading \/ p \in writing
  /\ reading' = reading \ {p}
  /\ writing' = writing \ {p}
  /\ UNCHANGED <<queue>>

Next ==
  \/ \E mode \in {"r", "w"}, p \in 1..NumActors : Request(mode, p)
  \/ BeginAccess
  \/ \E p \in 1..NumActors : StopActivity(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A mode \in {"r", "w"}, p \in 1..NumActors : WF_vars(Request(mode, p))
  /\ WF_vars(BeginAccess)
  /\ \A p \in 1..NumActors : WF_vars(StopActivity(p))

ReadersWritersFair == [pid |-> 1..NumActors, mode |-> {"r", "w"}]

Safety ==
  /\ (writing # {} => reading = {})
  /\ (reading # {} => writing = {})
  /\ Cardinality(writing) <= 1

Liveness ==
  /\ \A p \in 1..NumActors : (p \in reading) ~> (p \notin reading)
  /\ \A p \in 1..NumActors : (p \in writing) ~> (p \notin writing)

n == NumActors
====