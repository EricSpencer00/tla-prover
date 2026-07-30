---- MODULE Slush ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Node, SlushLoopProcess, SlushQueryProcess,
  HostMapping, SlushIterationCount, SampleSetSize,
  PickFlipThreshold, NoColor, NoMessage

\* Each node owns a loop process and a query process.  These triples form the
\* host mapping that ties everything together.
PROCESSES == SlushLoopProcess \cup SlushQueryProcess

Uncolored == "uncolored"
Colored == {"Red", "Blue"}
QueryMessage == [kind |-> "query", from |-> SlushLoopProcess, to |-> SlushQueryProcess, pc |-> Colored]
ReplyMessage == [kind |-> "reply", from |-> SlushQueryProcess, to |-> SlushLoopProcess, pc |-> Colored]
TermMessage == [kind |-> "term", from |-> SlushLoopProcess, to |-> SlushQueryProcess, pc |-> NoMessage]

VARIABLES assignment, inbox, pc, sample, loopIter, client

vars == <<assignment, inbox, pc, sample, loopIter, client>>

\* Replies collect in a set; the loop process waits until replies from every
\* sampled peer have arrived before it evaluates the round.
Replies == {m \in inbox : m.kind = "reply"}

TypeOK ==
  /\ assignment \in [Node -> Colored \cup {Uncolored}]
  /\ inbox \subseteq (QueryMessage \cup ReplyMessage \cup TermMessage)
  /\ pc \in [PROCESSES -> {"awaitingColor", "polling", "tallying", "done", "queryLoop"}]
  /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
  /\ loopIter \in [SlushLoopProcess -> 0..SlushIterationCount]
  /\ client \in {"ready", "done"}

Init ==
  /\ assignment = [n \in Node |-> Uncolored]
  /\ inbox = {}
  /\ pc = [p \in PROCESSES |-> IF p \in SlushLoopProcess THEN "awaitingColor" ELSE "queryLoop"]
  /\ sample = [p \in SlushLoopProcess |-> {}]
  /\ loopIter = [p \in SlushLoopProcess |-> 0]
  /\ client = "ready"

AssignColor ==
  /\ client = "ready"
  /\ \E n \in Node, c \in Colored :
       /\ assignment[n] = Uncolored
       /\ assignment' = [assignment EXCEPT ![n] = c]
  /\ client' = IF \A n \in Node : assignment[n] # Uncolored THEN "done" ELSE client
  /\ UNCHANGED <<inbox, pc, sample, loopIter>>

RequireColor(p) ==
  /\ pc[p] = "awaitingColor"
  /\ \E n \in Node :
       /\ <<p, n>> \in HostMapping
       /\ assignment[n] # Uncolored
  /\ pc' = [pc EXCEPT ![p] = "polling"]
  /\ UNCHANGED <<assignment, inbox, sample, loopIter, client>>

QuerySet(p) ==
  /\ pc[p] = "polling"
  /\ loopIter[p] < SlushIterationCount
  /\ sample' = [sample EXCEPT ![p] = {q \in SlushQueryProcess : q # p}]
  /\ inbox' = inbox \cup
       { [kind |-> "query", from |-> p, to |-> q,
          pc |-> assignment[CHOOSE n \in Node : <<p, n>> \in HostMapping]]
         : q \in {q \in SlushQueryProcess : q # p} }
  /\ pc' = [pc EXCEPT ![p] = "tallying"]
  /\ UNCHANGED <<assignment, loopIter, client>>

RespondQuery ==
  /\ \E m \in inbox : m.kind = "query"
  /\ LET m == CHOOSE m \in inbox : m.kind = "query"
         n == CHOOSE n \in Node : <<m.to, n>> \in HostMapping
     IN /\ assignment' = [assignment EXCEPT ![n] =
                            IF assignment[n] = Uncolored THEN m.pc ELSE assignment[n]]
        /\ inbox' = (inbox \ {m})
             \cup {[kind |-> "reply", from |-> m.to, to |-> m.from, pc |-> assignment[n]]}
        /\ UNCHANGED <<pc, sample, loopIter, client>>

TallyReplies(p) ==
  /\ pc[p] = "tallying"
  /\ \A q \in sample[p] : \E r \in Replies : r.from = q
  /\ LET count(c) == Cardinality({r \in Replies : r.from \in sample[p] /\ r.pc = c})
         n == CHOOSE n \in Node : <<p, n>> \in HostMapping
         top == {c \in Colored : count(c) >= PickFlipThreshold}
     IN /\ assignment' = [assignment EXCEPT ![n] = IF top = {} THEN assignment[n] ELSE CHOOSE c \in top : TRUE]
        /\ inbox' = {m \in inbox : m.from \notin sample[p]}
        /\ sample' = [sample EXCEPT ![p] = {}]
        /\ loopIter' = [loopIter EXCEPT ![p] = @ + 1]
        /\ pc' = IF loopIter[p] + 1 < SlushIterationCount
                   THEN [pc EXCEPT ![p] = "polling"]
                   ELSE [pc EXCEPT ![p] = "done"]
        /\ UNCHANGED client

TerminateLoop(p) ==
  /\ pc[p] = "done"
  /\ \A q \in SlushQueryProcess :
       inbox' = inbox \cup {[kind |-> "term", from |-> p, to |-> q, pc |-> NoMessage]}
  /\ UNCHANGED <<assignment, pc, sample, loopIter, client>>

ExitQueryLoop ==
  /\ pc["r1"] = "queryLoop"
  /\ \A p \in SlushLoopProcess : pc[p] = "done"
  /\ \A m \in inbox : m.kind = "term"
  /\ pc' = [pc EXCEPT !["r1"] = "done"]
  /\ UNCHANGED <<assignment, inbox, sample, loopIter, client>>

Next ==
  \/ AssignColor \/ RespondQuery \/ ExitQueryLoop
  \/ \E p \in SlushLoopProcess :
       \/ RequireColor(p) \/ QuerySet(p) \/ TallyReplies(p) \/ TerminateLoop(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(RespondQuery)

\* Every process eventually reaches its done state.
Termination == <>(pc["r1"] = "done")
====