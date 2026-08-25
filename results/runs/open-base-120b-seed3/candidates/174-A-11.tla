---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*-----------------------------------------------------------------
  Constants (to be instantiated by the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS
    Node,                \* Set of node identifiers
    SlushLoopProcess,    \* Set of loop process identifiers
    SlushQueryProcess,   \* Set of query process identifiers
    HostMapping,         \* Set of triples <<node, loop, query>>
    SlushIterationCount, \* Number of iterations each loop performs
    SampleSetSize,       \* Size of the peer sample taken each round
    PickFlipThreshold,   \* Minimum number of equal replies needed to flip
    NoColor,             \* Sentinel value for an uncolored node
    NoMessage             \* Sentinel value for “no message”

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
ColorSet == {0, 1}

MessageSet ==
    { [type |-> "query", src |-> SlushLoopProcess, dst |-> SlushQueryProcess,
       col |-> (NoColor \cup ColorSet)] } \/
    { [type |-> "reply", src |-> SlushQueryProcess, dst |-> SlushLoopProcess,
       col |-> (NoColor \cup ColorSet)] } \/
    { [type |-> "term",  src |-> SlushLoopProcess, dst |-> SlushQueryProcess] }

(*-----------------------------------------------------------------
  Helper functions
-----------------------------------------------------------------*)
HostNodeOfLoop(p) ==
    CHOOSE n \in Node : <<n, p, _>> \in HostMapping

HostNodeOfQuery(q) ==
    CHOOSE n \in Node : <<n, _, q>> \in HostMapping

QueryProcessOfNode(n) ==
    { q \in SlushQueryProcess : <<n, _, q>> \in HostMapping }

LoopProcessOfNode(n) ==
    { p \in SlushLoopProcess : <<n, p, _>> \in HostMapping }

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    color,      \* [node -> (NoColor \cup ColorSet)]
    msgs,       \* Set of in‑flight messages
    sample,     \* [loopProc -> SUBSET Node]  (current peer sample)
    iter,       \* [loopProc -> Nat]          (iterations completed)
    loopDone,   \* [loopProc -> BOOLEAN]     (has the loop terminated?)
    queryDone   \* [queryProc -> BOOLEAN]    (has the query process terminated?)

vars == <<color, msgs, sample, iter, loopDone, queryDone>>

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ iter   = [p \in SlushLoopProcess |-> 0]
    /\ loopDone = [p \in SlushLoopProcess |-> FALSE]
    /\ queryDone = [q \in SlushQueryProcess |-> FALSE]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)

(* 1. Client assigns a random color to an uncolored node *)
ClientAssign ==
    /\ \E n \in Node :
          /\ color[n] = NoColor
          /\ \E c \in ColorSet :
                /\ color' = [color EXCEPT ![n] = c]
                /\ UNCHANGED <<msgs, sample, iter, loopDone, queryDone>>
    /\ UNCHANGED << >>

(* 2. Loop process samples peers and sends queries *)
LoopSample ==
    /\ \E p \in SlushLoopProcess :
          LET n == HostNodeOfLoop(p) IN
          /\ color[n] # NoColor                       \* node already colored
          /\ iter[p] < SlushIterationCount
          /\ sample[p] = {}                           \* not currently sampling
          /\ \E peers \subseteq Node \ {n} :
                /\ Cardinality(peers) = SampleSetSize
                /\ LET qset == { q \in SlushQueryProcess :
                                   \E m \in peers : q \in QueryProcessOfNode(m) } IN
                   /\ msgs' = msgs \cup {
                        [type |-> "query",
                         src  |-> p,
                         dst  |-> q,
                         col  |-> color[n]]
                         : q \in qset
                     }
                   /\ sample' = [sample EXCEPT ![p] = peers]
                   /\ UNCHANGED <<color, iter, loopDone, queryDone>>
    /\ UNCHANGED << >>

(* 3. Query process receives a query, possibly adopts the color, and replies *)
QueryRespond ==
    /\ \E m \in msgs :
          /\ m.type = "query"
          /\ LET q == m.dst
                 p == m.src
                 n == HostNodeOfQuery(q) IN
          /\ IF color[n] = NoColor THEN
                color' = [color EXCEPT ![n] = m.col]
             ELSE
                UNCHANGED color
          /\ msgs' = (msgs \ {m}) \cup {
                [type |-> "reply",
                 src  |-> q,
                 dst  |-> p,
                 col  |-> color[n]]
            }
          /\ UNCHANGED <<sample, iter, loopDone, queryDone>>
    /\ UNCHANGED << >>

(* 4. Loop process tallies replies and possibly flips its node's color *)
LoopTally ==
    /\ \E p \in SlushLoopProcess :
          LET n == HostNodeOfLoop(p) IN
          /\ sample[p] # {}                                 \* a sample is in progress
          /\ \A q \in { q \in SlushQueryProcess :
                         \E m \in Node : m \in sample[p] /\ q \in QueryProcessOfNode(m) } :
                \E r \in msgs :
                     /\ r.type = "reply"
                     /\ r.dst  = p
                     /\ r.src  = q
          /\ LET replies == { r \in msgs :
                               r.type = "reply" /\ r.dst = p } IN
             cnt0 == Cardinality({ r \in replies : r.col = 0 })
             cnt1 == Cardinality({ r \in replies : r.col = 1 }) IN
          /\ IF cnt0 >= PickFlipThreshold THEN
                 color' = [color EXCEPT ![n] = 0]
             ELSE IF cnt1 >= PickFlipThreshold THEN
                 color' = [color EXCEPT ![n] = 1]
             ELSE
                 UNCHANGED color
          /\ msgs'   = msgs \ replies
          /\ sample' = [sample EXCEPT ![p] = {}]
          /\ iter'   = [iter EXCEPT ![p] = @ + 1]
          /\ UNCHANGED <<loopDone, queryDone>>
    /\ UNCHANGED << >>

(* 5. Loop process terminates after completing all iterations *)
LoopTerminate ==
    /\ \E p \in SlushLoopProcess :
          /\ iter[p] = SlushIterationCount
          /\ ~loopDone[p]
          /\ msgs' = msgs \cup {
                [type |-> "term",
                 src  |-> p,
                 dst  |-> q] : q \in SlushQueryProcess
            }
          /\ loopDone' = [loopDone EXCEPT ![p] = TRUE]
          /\ UNCHANGED <<color, sample, iter, queryDone>>
    /\ UNCHANGED << >>

(* 6. Query process handles termination messages and exits when all loops are done *)
QueryTerminate ==
    /\ \E q \in SlushQueryProcess :
          /\ \E m \in msgs :
                /\ m.type = "term"
                /\ m.dst = q
                /\ msgs' = msgs \ {m}
                /\ IF \A p \in SlushLoopProcess : loopDone[p] THEN
                       queryDone' = [queryDone EXCEPT ![q] = TRUE]
                   ELSE
                       UNCHANGED queryDone
                /\ UNCHANGED <<color, sample, iter, loopDone>>
    /\ UNCHANGED << >>

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ ClientAssign
    \/ LoopSample
    \/ QueryRespond
    \/ LoopTally
    \/ LoopTerminate
    \/ QueryTerminate

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Type invariant
-----------------------------------------------------------------*)
TypeInvariant ==
    /\ color \in [Node -> (NoColor \cup ColorSet)]
    /\ msgs \subseteq MessageSet
    /\ sample \in [SlushLoopProcess -> SUBSET Node]
    /\ iter \in [SlushLoopProcess -> Nat]
    /\ loopDone \in [SlushLoopProcess -> BOOLEAN]
    /\ queryDone \in [SlushQueryProcess -> BOOLEAN]

====