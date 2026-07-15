---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  Constants (to be bound in the .cfg file)
--------------------------------------------------------------------*)
CONSTANT Node
CONSTANT SlushLoopProcess
CONSTANT SlushQueryProcess
CONSTANT HostMapping          \* set of triples <<loop, query, node>>
CONSTANT SlushIterationCount
CONSTANT SampleSetSize
CONSTANT PickFlipThreshold
CONSTANT NoColor
CONSTANT NoMessage

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
Colors == {0, 1}
LoopSet == SlushLoopProcess
QuerySet == SlushQueryProcess
NodeSet == Node

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    col,            \* [node -> Colors \cup {NoColor}]
    msgs,           \* set of messages in flight
    pc,             \* [proc -> pc value]
    sample,         \* [loop -> SUBSET QuerySet]   (current sample set)
    iter            \* [loop -> Nat]               (iterations done)

(*--------------------------------------------------------------------
  Message definitions
--------------------------------------------------------------------*)
Message == [type : {"query", "reply", "term"},
            from : (LoopSet \cup QuerySet),
            to   : (LoopSet \cup QuerySet),
            body : (Colors \cup {NoMessage})]

QueryMsg   == [type |-> "query", from |-> self, to |-> q, body |-> c] \* self is a loop process, q a query process, c its current color
ReplyMsg   == [type |-> "reply", from |-> self, to |-> l, body |-> c] \* self is a query process, l a loop process, c its current color
TermMsg    == [type |-> "term",  from |-> self, to |-> q, body |-> NoMessage] \* self is a loop process, q a query process

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
LoopHost(l) == 
    CASE \E <<l, q, n>> \in HostMapping : n
    OTHER -> NoMessage

QueryHost(q) == 
    CASE \E <<l, q, n>> \in HostMapping : n
    OTHER -> NoMessage

(* A process is either a loop or a query *)
Proc == LoopSet \cup QuerySet

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ col = [n \in NodeSet |-> NoColor]
    /\ msgs = {}
    /\ pc = [p \in Proc |-> 
                IF p \in LoopSet THEN "awaitColor"
                ELSE "replyLoop"]
    /\ sample = [l \in LoopSet |-> {}]
    /\ iter = [l \in LoopSet |-> 0]

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)

(* 1. Client assigns a color to an uncolored node *)
ClientAssign ==
    \E n \in NodeSet :
        /\ col[n] = NoColor
        /\ col' = [col EXCEPT ![n] = CHOOSE c \in Colors : TRUE]
        /\ UNCHANGED <<msgs, pc, sample, iter>>

(* 2. Loop process waits for its node to be colored *)
RequireColor(l) ==
    /\ pc[l] = "awaitColor"
    /\ col[LoopHost(l)] # NoColor
    /\ pc' = [pc EXCEPT ![l] = "sample"]
    /\ UNCHANGED <<col, msgs, sample, iter>>

(* 3. Loop process selects a random sample of query processes and sends queries *)
QuerySample(l) ==
    /\ pc[l] = "sample"
    /\ sample[l] = {}
    /\ LET candidates == QuerySet \ { QueryOfLoop(l) } IN
       sample' = [sample EXCEPT ![l] = 
           CHOOSE s \subseteq candidates : Cardinality(s) = SampleSetSize]
    /\ msgs' = msgs \cup {
        [type |-> "query", from |-> l, to |-> q, body |-> col[LoopHost(l)]]
        : q \in sample'[l] }
    /\ pc' = [pc EXCEPT ![l] = "awaitReplies"]
    /\ UNCHANGED <<col, iter>>

(* Helper: the query process belonging to a loop process *)
QueryOfLoop(l) ==
    CHOOSE q \in QuerySet : <<l, q, LoopHost(l)>> \in HostMapping

(* 4. Query process receives a query, possibly adopts its color, and replies *)
RespondToQuery(q) ==
    \E m \in msgs :
        /\ m.type = "query"
        /\ m.to = q
        /\ LET n == QueryHost(q) IN
           /\ IF col[n] = NoColor THEN
                 col' = [col EXCEPT ![n] = m.body]
              ELSE col' = col
        /\ msgs' = (msgs \ {m}) \cup {
                [type |-> "reply", from |-> q, to |-> m.from, body |-> col[n]] }
        /\ pc' = [pc EXCEPT ![q] = "replyLoop"]  \* stays in replyLoop after replying
        /\ UNCHANGED <<sample, iter>>

(* 5. Loop process tallies replies and possibly flips its node's color *)
TallyReplies(l) ==
    /\ pc[l] = "awaitReplies"
    /\ \A q \in sample[l] : 
          \E r \in msgs : r.type = "reply" /\ r.from = q /\ r.to = l
    /\ LET replies == { r.body : r \in msgs : r.type = "reply" /\ r.to = l } IN
       LET cnt(c) == Cardinality({ r \in replies : r = c }) IN
       /\ IF cnt(0) >= PickFlipThreshold THEN
            col' = [col EXCEPT ![LoopHost(l)] = 0]
          ELSE IF cnt(1) >= PickFlipThreshold THEN
            col' = [col EXCEPT ![LoopHost(l)] = 1]
          ELSE col' = col
    /\ msgs' = msgs \ { r \in msgs : r.type = "reply" /\ r.to = l }
    /\ iter' = [iter EXCEPT ![l] = @ + 1]
    /\ IF iter'[l] < SlushIterationCount THEN
            pc' = [pc EXCEPT ![l] = "sample"]
        ELSE
            /\ pc' = [pc EXCEPT ![l] = "done"]
            /\ msgs' = msgs' \cup {
                 [type |-> "term", from |-> l, to |-> q, body |-> NoMessage]
                 : q \in QuerySet }
    /\ sample' = [sample EXCEPT ![l] = {}]
    /\ UNCHANGED <<col, sample, iter>>

(* 6. Loop termination broadcast already handled in TallyReplies when done *)

(* 7. Query processes exit when all loop processes are done *)
QueryExit(q) ==
    /\ pc[q] = "replyLoop"
    /\ \A l \in LoopSet : pc[l] = "done"
    /\ pc' = [pc EXCEPT ![q] = "done"]
    /\ UNCHANGED <<col, msgs, sample, iter>>

(* 8. No‑op for processes already done *)
NoOp(p) ==
    /\ pc[p] = "done"
    /\ UNCHANGED <<col, msgs, pc, sample, iter>>

(*--------------------------------------------------------------------
  Next-state relation
--------------------------------------------------------------------*)
Next ==
    \/ \E n \in NodeSet : ClientAssign
    \/ \E l \in LoopSet : RequireColor(l)
    \/ \E l \in LoopSet : QuerySample(l)
    \/ \E q \in QuerySet : RespondToQuery(q)
    \/ \E l \in LoopSet : TallyReplies(l)
    \/ \E q \in QuerySet : QueryExit(q)
    \/ \E p \in Proc : NoOp(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<col, msgs, pc, sample, iter>>

(*--------------------------------------------------------------------
  Type invariant (safety property)
--------------------------------------------------------------------*)
TypeInvariant ==
    /\ col \in [NodeSet -> (Colors \cup {NoColor})]
    /\ msgs \subseteq Message
    /\ pc \in [Proc -> {"awaitColor", "sample", "awaitReplies",
                       "replyLoop", "done"}]
    /\ sample \in [LoopSet -> SUBSET QuerySet]
    /\ iter \in [LoopSet -> Nat]
    /\ \A l \in LoopSet :
         (pc[l] = "awaitColor") => col[LoopHost(l)] # NoColor
    /\ \A q \in QuerySet :
         (pc[q] = "replyLoop") => TRUE   \* placeholder, always true

=============================================================================