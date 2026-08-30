---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Choice == {"read", "write"}
Modes == {"idle", "reading", "writing"}

VARIABLES readers, writers, queue, mode

vars == <<readers, writers, queue, mode>>

TypeOK ==
  /\ readers \subseteq NumActors
  /\ writers \subseteq NumActors
  /\ queue \in Seq([who : NumActors, mode : Choice])
  /\ mode \in [NumActors -> Modes]

Init ==
  /\ readers = {}
  /\ writers = {}
  /\ queue = << >>
  /\ mode = [a \in NumActors |-> "idle"]

RequestRead(a) ==
  /\ \A i \in 1..Len(queue) : ~(queue[i].who = a /\ queue[i].mode = "read")
  /\ queue' = Append(queue, [who |-> a, mode |-> "read"])
  /\ UNCHANGED <<readers, writers, mode>>

RequestWrite(a) ==
  /\ \A i \in 1..Len(queue) : ~(queue[i].who = a /\ queue[i].mode = "write")
  /\ queue' = Append(queue, [who |-> a, mode |-> "write"])
  /\ UNCHANGED <<readers, writers, mode>>

BeginReadWrite ==
  /\ Len(queue) > 0
  /\ writers = {}
  /\ LET h == Head(queue) IN
       \/ (h.mode = "read" /\ mode[h.who] = "idle")
          /\ readers' = readers \cup {h.who}
          /\ mode' = [mode EXCEPT ![h.who] = "reading"]
       \/ (h.mode = "write" /\ readers = {} /\ mode[h.who] = "idle")
          /\ writers' = writers \cup {h.who}
          /\ mode' = [mode EXCEPT ![h.who] = "writing"]
  /\ queue' = Tail(queue)

StopActivity(a) ==
  /\ mode[a] \in {"reading", "writing"}
  /\ readers' = readers \ {a}
  /\ writers' = writers \ {a}
  /\ mode' = [mode EXCEPT ![a] = "idle"]
  /\ UNCHANGED queue

Next ==
  \/ BeginReadWrite
  \/ \E a \in NumActors : RequestRead(a) \/ RequestWrite(a) \/ StopActivity(a)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(BeginReadWrite)
        /\ \A a \in NumActors : SF_vars(RequestRead(a)) /\ SF_vars(RequestWrite(a)) /\ SF_vars(StopActivity(a))

\* Readers and writers are never simultaneously active, and at most one writer
\* is active at any time.
Safety ==
  /\ (writers # {} => readers = {})
  /\ (readers # {} => writers = {})
  /\ \A w1, w2 \in writers : w1 = w2

Liveness ==
  /\ \A a \in NumActors : (mode[a] = "idle") ~> (mode[a] = "reading")
  /\ \A a \in NumActors : (mode[a] = "idle") ~> (mode[a] = "writing")
  /\ \A a \in NumActors : (mode[a] = "reading") ~> (mode[a] = "idle")
  /\ \A a \in NumActors : (mode[a] = "writing") ~> (mode[a] = "idle")

n == {1, 2}

====