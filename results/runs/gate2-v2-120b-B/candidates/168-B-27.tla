---- MODULE ReadersWriters ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

VARIABLES
    readers, \* set of processes currently reading
    writers, \* set of processes currently writing
    waiting  \* queue of processes waiting to access the resource

vars == <<readers, writers, waiting>>

Actors == 1..NumActors

\* Convert a sequence of pairs to a set of the pairs
ToSet(s) == { s[i] : i \in DOMAIN s }

\* Predicates on a pair
read(s)  == s[1] = "read"
write(s) == s[1] = "write"

\* Helper to select subsequence matching a predicate
SelectSeq(seq, pred) ==
    [i \in DOMAIN seq |-> IF pred(seq[i]) THEN seq[i] ELSE NULL] \ {NULL}

WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, read)) }

WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, write)) }

-----------------------------------------------------------------------------
(* Actions *)
TryRead(actor) ==
    /\ actor \notin WaitingToRead
    /\ waiting' = Append(waiting, <<"read", actor>>)
    /\ UNCHANGED <<readers, writers>>

TryWrite(actor) ==
    /\ actor \notin WaitingToWrite
    /\ waiting' = Append(waiting, <<"write", actor>>)
    /\ UNCHANGED <<readers, writers>>

Read(actor) ==
    /\ waiting # <<>>
    /\ waiting[1][1] = "read"
    /\ waiting[1][2] = actor
    /\ readers' = readers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

Write(actor) ==
    /\ waiting # <<>>
    /\ waiting[1][1] = "write"
    /\ waiting[1][2] = actor
    /\ writers' = writers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

ReadOrWrite ==
    /\ waiting # <<>>
    /\ writers = {}
    /\ LET pair == Head(waiting)
           actor == pair[2]
       IN IF pair[1] = "read"
          THEN Read(actor)
          ELSE Write(actor)

StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

Stop == \E actor \in (readers \cup writers) : StopActivity(actor)

-----------------------------------------------------------------------------
(* Specification *)
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

Next ==
    \/ \E actor \in Actors : TryRead(actor)
    \/ \E actor \in Actors : TryWrite(actor)
    \/ ReadOrWrite
    \/ Stop

Fairness ==
    /\ \A actor \in Actors : WF_vars(TryRead(actor))
    /\ \A actor \in Actors : WF_vars(TryWrite(actor))
    /\ WF_vars(ReadOrWrite)
    /\ WF_vars(Stop)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Invariants *)
TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({ "read", "write" } \X Actors)

Safety ==
    /\ ~(readers # {} /\ writers # {})
    /\ Cardinality(writers) <= 1

=============================================================================