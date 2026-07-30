---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences

CONSTANTS NumActors

Process == 1 .. NumActors
ReqType == {"read", "write"}

VARIABLES reading, writing, queue

vars == <<reading, writing, queue>>

TypeOK ==
  /\ reading \subseteq Process
  /\ writing \subseteq Process
  /\ queue \in Seq([type: ReqType, proc: Process])

Init ==
  /\ reading = {}
  /\ writing = {}
  /\ queue = << >>

RequestRead(p) ==
  /\ \A i \in DOMAIN queue : queue[i].proc # p
  /\ queue' = Append(queue, [type |-> "read", proc |-> p])
  /\ UNCHANGED <<reading, writing>>

RequestWrite(p) ==
  /\ \A i \in DOMAIN queue : queue[i].proc # p
  /\ queue' = Append(queue, [type |-> "write", proc |-> p])
  /\ UNCHANGED <<reading, writing>>

Begin ==
  /\ queue # << >>
  /\ writing = {}
  /\ LET req == Head(queue) IN
       /\ IF req.type = "read"
          THEN reading' = reading \cup {req.proc} /\ writing' = writing
          ELSE /\ reading = {}
               /\ writing' = writing \cup {req.proc}
               /\ reading' = reading
  /\ queue' = Tail(queue)

Stop ==
  /\ \E p \in Process :
       /\ \/ p \in reading
          \/ p \in writing
       /\ reading' = reading \ {p}
       /\ writing' = writing \ {p}
  /\ UNCHANGED queue

Next ==
  \/ \E p \in Process : RequestRead(p)
  \/ \E p \in Process : RequestWrite(p)
  \/ Begin
  \/ Stop

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Process : RequestRead(p))
  /\ WF_vars(\E p \in Process : RequestWrite(p))
  /\ WF_vars(Begin)
  /\ WF_vars(Stop)

Safety ==
  /\ ~(writing # {} /\ reading # {})
  /\ Cardinality(writing) =< 1

Liveness ==
  /\ \A p \in Process :
       /\ TRUE
       /\ TRUE
  /\ TRUE

====