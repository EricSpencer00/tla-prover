---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

\* -------------------------------------------------
\* Constants (to be instantiated by the .cfg file)
\* -------------------------------------------------
CONSTANTS
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* Set of loop-process identifiers
    SlushQueryProcess,  \* Set of query-process identifiers
    HostMapping,        \* Set of triples (<<process, role, node>>)
    SlushIterationCount,\* Maximum number of iterations each loop may perform
    SampleSetSize,      \* Size of the random peer sample taken each round
    PickFlipThreshold,  \* Minimum number of identical replies needed to adopt a color
    NoColor,            \* Special value meaning “uncolored”
    NoMessage           \* Special value meaning “no message” (used as a placeholder)

\* -------------------------------------------------
\* Derived sets and helper definitions
\* -------------------------------------------------
Colors == {"Red", "Blue"}

ProcessRoles == {"Loop", "Query"}

\* Mapping from a loop process to its host node
LoopHost(p) == 
    CHOOSE n \in Node : <<p, "Loop", n>> \in HostMapping

\* Mapping from a query process to its host node
QueryHost(p) ==
    CHOOSE n \in Node : <<p, "Query", n>> \in HostMapping

\* The set of all message records
Message == 
    [type : {"Query", "Reply", "Terminate"},
     src  : SlushLoopProcess \cup SlushQueryProcess,
     dst  : SlushLoopProcess \cup SlushQueryProcess,
     payload : BOOLEAN \cup Colors]

\* Message constructors (for readability)
QueryMsg(src, dst, col)   == [type |-> "Query",   src |-> src, dst |-> dst, payload |-> col]
ReplyMsg(src, dst, col)   == [type |-> "Reply",   src |-> src, dst |-> dst, payload |-> col]
TermMsg(src, dst)         == [type |-> "Terminate",src |-> src, dst |-> dst, payload |-> FALSE]

\* -------------------------------------------------
\* Variables
\* -------------------------------------------------
VARIABLES
    colors,          \* [node -> Colors \cup {NoColor}]
    msgs,            \* Set of in‑flight messages
    pc,              \* [process -> Nat]  (program counter)
    sampleSet,       \* [loopProc -> SUBSET SlushQueryProcess]
    iterCount,       \* [loopProc -> Nat]
    pendingReplies   \* [loopProc -> SUBSET SlushQueryProcess]

\* -------------------------------------------------
\* Initial state
\* -------------------------------------------------
Init ==
    /\ colors = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ pc = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> 0]
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]
    /\ iterCount = [lp \in SlushLoopProcess |-> 0]
    /\ pendingReplies = [lp \in SlushLoopProcess |-> {}]

\* -------------------------------------------------
\* Actions
\* -------------------------------------------------

\* 1. Client assigns a random color to an uncolored node
ClientAssign ==
    /\ pc["Client"] = 0
    /\ \E n \in Node :
          /\ colors[n] = NoColor
          /\ colors' = [colors EXCEPT ![n] = CHOOSE c \in Colors : TRUE]
    /\ \A p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) : pc'[p] = pc[p]
    /\ UNCHANGED << msgs, sampleSet, iterCount, pendingReplies >>

ClientDone ==
    /\ pc["Client"] = 0
    /\ colors[n] # NoColor  \* all nodes already colored
    /\ pc' = [pc EXCEPT !["Client"] = 1]
    /\ UNCHANGED << colors, msgs, sampleSet, iterCount, pendingReplies >>

\* 2. Loop process waits until its host node is colored
WaitForColor(lp) ==
    LET n == LoopHost(lp) IN
    /\ pc[lp] = 0
    /\ colors[n] # NoColor
    /\ pc' = [pc EXCEPT ![lp] = 1]
    /\ UNCHANGED << colors, msgs, sampleSet, iterCount, pendingReplies >>

\* 3. Loop process selects a random sample and sends query messages
SendQueries(lp) ==
    LET n == LoopHost(lp) IN
    /\ pc[lp] = 1
    /\ sampleSet[lp] = {}
    /\ \E s \in SUBSET SlushQueryProcess :
          /\ Cardinality(s) = SampleSetSize
          /\ sampleSet' = [sampleSet EXCEPT ![lp] = s]
          /\ msgs' = msgs \cup { QueryMsg(lp, q, colors[n]) : q \in s }
    /\ pc' = [pc EXCEPT ![lp] = 2]
    /\ pendingReplies' = [pendingReplies EXCEPT ![lp] = s]
    /\ UNCHANGED << colors, iterCount >>

\* 4. Query process receives a query, possibly adopts the color, and replies
ReceiveAndReply(qp) ==
    /\ pc[qp] = 0
    /\ \E m \in msgs :
          /\ m.type = "Query"
          /\ m.dst = qp
          /\ LET n == QueryHost(qp) IN
                /\ colors' = 
                     IF colors[n] = NoColor 
                        THEN [colors EXCEPT ![n] = m.payload]
                        ELSE colors
                /\ msgs' = (msgs \ {m}) \cup { ReplyMsg(qp, m.src, colors'[n]) }
    /\ pc' = [pc EXCEPT ![qp] = 0]   \* stays at 0, ready for next query
    /\ UNCHANGED << sampleSet, iterCount, pendingReplies >>

\* 5. Loop process processes a reply
ProcessReply(lp) ==
    /\ pc[lp] = 2
    /\ \E m \in msgs :
          /\ m.type = "Reply"
          /\ m.dst = lp
          /\ pendingReplies[lp] # {}   \* there is at least one pending reply
          /\ pendingReplies' = [pendingReplies EXCEPT ![lp] = pendingReplies[lp] \ {m.src}]
          /\ msgs' = msgs \ {m}
          /\ IF pendingReplies' [lp] = {} 
                THEN 
                     /\ iterCount' = [iterCount EXCEPT ![lp] = iterCount[lp] + 1]
                     /\ \* Tally the replies that have been collected in this round
                        \* For simplicity we recompute the tally directly from the replies
                        \* that have just been removed from the message set.
                        LET n == LoopHost(lp) IN
                        LET replies == { r \in msgs : r.type = "Reply" /\ r.dst = lp } \cup { m } IN
                        LET reds   == Cardinality({ r \in replies : r.payload = "Red" }) IN
                        LET blues  == Cardinality({ r \in replies : r.payload = "Blue" }) IN
                        /\ IF reds >= PickFlipThreshold 
                               THEN colors' = [colors EXCEPT ![n] = "Red"]
                               ELSE IF blues >= PickFlipThreshold 
                                      THEN colors' = [colors EXCEPT ![n] = "Blue"]
                                      ELSE colors'
                ELSE UNCHANGED colors
    /\ pc' = [pc EXCEPT ![lp] = 2]   \* stay in same step until all replies received
    /\ UNCHANGED << sampleSet >>

\* 6. After reaching the maximum iteration count, the loop process terminates
LoopTerminate(lp) ==
    LET n == LoopHost(lp) IN
    /\ pc[lp] = 2
    /\ iterCount[lp] >= SlushIterationCount
    /\ msgs' = msgs \cup { TermMsg(lp, qp) : qp \in SlushQueryProcess }
    /\ pc' = [pc EXCEPT ![lp] = 3]
    /\ UNCHANGED << colors, sampleSet, iterCount, pendingReplies >>

LoopDone(lp) ==
    /\ pc[lp] = 3
    /\ pc' = [pc EXCEPT ![lp] = 4]
    /\ UNCHANGED << colors, msgs, sampleSet, iterCount, pendingReplies >>

\* 7. Query processes exit when all loop processes have terminated
QueryExit(qp) ==
    /\ pc[qp] = 0
    /\ \A lp \in SlushLoopProcess : pc[lp] >= 4
    /\ pc' = [pc EXCEPT ![qp] = 1]
    /\ UNCHANGED << colors, msgs, sampleSet, iterCount, pendingReplies >>

\* No‑op step to keep the model from deadlocking when everything is done
Stutter ==
    UNCHANGED << colors, msgs, pc, sampleSet, iterCount, pendingReplies >>

\* -------------------------------------------------
\* Next-state relation
\* -------------------------------------------------
Next ==
    \/ ClientAssign
    \/ ClientDone
    \/ \E lp \in SlushLoopProcess : WaitForColor(lp)
    \/ \E lp \in SlushLoopProcess : SendQueries(lp)
    \/ \E qp \in SlushQueryProcess : ReceiveAndReply(qp)
    \/ \E lp \in SlushLoopProcess : ProcessReply(lp)
    \/ \E lp \in SlushLoopProcess : LoopTerminate(lp)
    \/ \E lp \in SlushLoopProcess : LoopDone(lp)
    \/ \E qp \in SlushQueryProcess : QueryExit(qp)
    \/ Stutter

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec == Init /\ [][Next]_<<colors, msgs, pc, sampleSet, iterCount, pendingReplies>>

\* -------------------------------------------------
\* Type invariant (required by the .cfg)
\* -------------------------------------------------
TypeInvariant ==
    /\ colors \in [Node -> (Colors \cup {NoColor})]
    /\ msgs \subseteq Message
    /\ pc \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) -> Nat]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iterCount \in [SlushLoopProcess -> Nat]
    /\ pendingReplies \in [SlushLoopProcess -> SUBSET SlushQueryProcess]

\* -------------------------------------------------
\* THEOREM (optional, not required by the .cfg but useful)
\* -------------------------------------------------
THEOREM Spec => []TypeInvariant

====