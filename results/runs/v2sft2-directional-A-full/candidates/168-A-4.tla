---- MODULE ReadersWriters ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

\* Types
Actor == 1..NumActors

\* Request type: a record with fields `who` and `type`
Request == [who : Actor, type : {"Read", "Write"}]

\* Variables
VARIABLES R, W, Q

\* Helper definitions
ReadReq(q) == (q.type = "Read")
WriteReq(q) == (q.type = "Write")

NoWrite == W = {}
NoRead  == R = {}

\* Initial state
Init ==
    /\ R = {}
    /\ W = {}
    /\ Q = <<>>

\* Request to read: a non-waiting process appends a read request
ReqRead(p) ==
    /\ p \notin R
    /\ p \notin W
    /\ \A q \in Q : q.who # p
    /\ Q' = Append(Q, [who |-> p, type |-> "Read"])
    /\ UNCHANGED <<R, W>>

\* Request to write: a non-waiting process appends a write request
ReqWrite(p) ==
    /\ p \notin R
    /\ p \notin W
    /\ \A q \in Q : q.who # p
    /\ Q' = Append(Q, [who |-> p, type |-> "Write"])
    /\ UNCHANGED <<R, W>>

\* Process the queue: the front request is examined
ProcessQueue ==
    /\ Q # <<>>
    /\ \E q \in Q :
        /\ q = Head(Q)
        /\ IF ReadReq(q) THEN
              /\ NoWrite
              /\ R' = R \cup {q.who}
              /\ W' = W
          ELSE IF WriteReq(q) THEN
              /\ NoRead
              /\ W' = W \cup {q.who}
              /\ R' = R
          ELSE
              UNCHANGED <<R, W>>
    /\ Q' = Tail(Q)

\* Stop activity: a reader or writer may stop
Stop(p) ==
    \/ /\ p \in R
       /\ R' = R \ {p}
       /\ W' = W
    \/ /\ p \in W
       /\ W' = W \ {p}
       /\ R' = R
    /\ UNCHANGED Q

\* Next-state relation
Next ==
    \E p \in Actor :
        \/ ReqRead(p)
        \/ ReqWrite(p)
        \/ Stop(p)
    \/ ProcessQueue

\* Specification
Spec == Init /\ [][Next]_<<R, W, Q>>

\* Type invariant (optional, for TLC)
TypeOK ==
    /\ R \subsetof Actor
    /\ W \subsetof Actor
    /\ Q \in Seq(Request)

\* Safety invariant: readers and writers are never simultaneously active, and at most one writer
Safety ==
    /\ (|W| <= 1)
    /\ (W = {} \/ R = {})

\* Liveness property: every process eventually acts (requests and stops)
Liveness == WF_acts(Next)

====