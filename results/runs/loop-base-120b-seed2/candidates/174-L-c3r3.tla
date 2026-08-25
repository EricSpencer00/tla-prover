---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Node,\* set of node identifiers
    SlushLoopProcess,\* set of loop process identifiers (one per node)
    SlushQueryProcess,\* set of query process identifiers (one per node)
    HostMapping,\* set of triples (either tuples <<node,loop,query>> or 3‑element sets {node,loop,query})
    SlushIterationCount,\* number of iterations each loop process must perform
    SampleSetSize,\* size of the random sample taken each iteration
    PickFlipThreshold,\* threshold for adopting a color
    NoColor,\* value denoting an uncolored node
    NoMessage \* value (unused, required by the configuration)

\*=====================================================================
\*  Derived definitions
\*=====================================================================

\* Set of possible colors (including the uncolored value)
Colors == {"Red", "Blue", NoColor}

\* Record type for messages
Message == [type  : {"query", "reply", "term"},
            src   : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
            dst   : (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}),
            col   : Colors]

\* The union of all identifiers that may appear inside a triple
AllElems == Node \cup SlushLoopProcess \cup SlushQueryProcess

\* Predicate that tells whether a value is a 3‑tuple (i.e., a function with domain 1..3)
IsTuple(t) == t \in [1..3 -> AllElems]

\* Helper that works for both tuple and set representations of a triple.
\* Returns TRUE iff element a appears in the triple t.
TripleContains(t, a) ==
    IF IsTuple(t) THEN
        a = t[1] \/ a = t[2] \/ a = t[3]
    ELSE
        a \in t

\* Mapping from a process identifier to its host node, using HostMapping.
\* Works whether HostMapping contains tuples <<n,l,q>> or 3‑element sets {n,l,q}.
HostNode(p) ==
    IF p \in SlushLoopProcess \cup SlushQueryProcess THEN
        CHOOSE n \in Node :
            \E t \in HostMapping :
                TripleContains(t, n) /\ TripleContains(t, p)
    ELSE NoColor

\* All possible sample sets that a given loop process may choose
SampleSet(lp) ==
    { S \in SUBSET { q \in SlushQueryProcess :
                        HostNode(q) # HostNode(lp) } :
          Cardinality(S) = SampleSetSize }

\*=====================================================================
\*  Variables
\*=====================================================================
VARIABLES
    color,   \* [node -> color] mapping
    msgs,    \* set of in‑flight messages
    pc,      \* program counter for each process (including "client")
    sample,  \* [loopProc -> set of queried query processes]
    iter     \* [loopProc -> number of completed iterations]

\*=====================================================================
\*  Initial state
\*=====================================================================
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ pc    = [p \in (SlushLoopProcess \cup SlushQueryProcess \cup {"client"}) |-> "Init"]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]

\*=====================================================================
\*  Actions
\*=====================================================================

\* (1) Client assigns a random color to an uncolored node
ClientAssign ==
    \E n \in Node :
        /\ color[n] = NoColor
        /\ \E c \in {"Red", "Blue"} :
               /\ color' = [color EXCEPT ![n] = c]
               /\ UNCHANGED <<msgs, pc, sample, iter>>

\* (2) Loop process selects a sample and sends queries
LoopSample ==
    \E lp \in SlushLoopProcess :
        LET myNode == HostNode(lp) IN
        /\ color[myNode] # NoColor
        /\ iter[lp] < SlushIterationCount
        /\ sample[lp] = {}
        /\ \E S \in SampleSet(lp) :
               /\ sample' = [sample EXCEPT ![lp] = S]
               /\ msgs'   = msgs \cup
                              { [type |-> "query",
                                 src  |-> lp,
                                 dst  |-> q,
                                 col  |-> color[myNode]] :
                                   q \in S }
               /\ UNCHANGED <<color, pc, iter>>

\* (3) Loop process tallies replies and possibly flips its node's color
LoopTally ==
    \E lp \in SlushLoopProcess :
        LET myNode == HostNode(lp) IN
        LET S      == sample[lp] IN
        LET replies == { m \in msgs :
                           m.type = "reply" /\ m.dst = lp } IN
        /\ color[myNode] # NoColor
        /\ iter[lp] < SlushIterationCount
        /\ S # {}
        /\ \A q \in S : \E r \in replies : r.src = q
        /\ LET redCnt  == Cardinality({ r \in replies : r.col = "Red" })
               blueCnt == Cardinality({ r \in replies : r.col = "Blue" }) IN
           IF redCnt >= PickFlipThreshold THEN
               color' = [color EXCEPT ![myNode] = "Red"]
           ELSE IF blueCnt >= PickFlipThreshold THEN
               color' = [color EXCEPT ![myNode] = "Blue"]
           ELSE
               UNCHANGED color
        /\ msgs'   = msgs \ replies
        /\ sample' = [sample EXCEPT ![lp] = {}]
        /\ iter'   = [iter EXCEPT ![lp] = @ + 1]
        /\ UNCHANGED pc

\* (4) Loop process finishes its allotted iterations and broadcasts termination
LoopTerminate ==
    \E lp \in SlushLoopProcess :
        LET myNode == HostNode(lp) IN
        /\ iter[lp] >= SlushIterationCount
        /\ msgs' = msgs \cup
                    { [type |-> "term",
                       src  |-> lp,
                       dst  |-> "client",
                       col  |-> NoColor] }
        /\ pc'   = [pc EXCEPT ![lp] = "Done"]
        /\ UNCHANGED <<color, sample, iter>>

\* (5) Query process receives a query, possibly adopts the queried color, and replies
QueryRespond ==
    \E qp \in SlushQueryProcess :
        LET myNode == HostNode(qp) IN
        /\ \E m \in msgs :
               m.type = "query" /\ m.dst = qp
        /\ LET qmsg == CHOOSE mm \in msgs :
                         mm.type = "query" /\ mm.dst = qp IN
           /\ IF color[myNode] = NoColor THEN
                  color' = [color EXCEPT ![myNode] = qmsg.col]
              ELSE
                  UNCHANGED color
           /\ msgs' = (msgs \ {qmsg}) \cup
                        { [type |-> "reply",
                           src  |-> qp,
                           dst  |-> qmsg.src,
                           col  |-> color[myNode]] }
           /\ UNCHANGED <<pc, sample, iter>>

\* (6) Query processes exit when all loop processes have terminated
QueryTerminate ==
    \E qp \in SlushQueryProcess :
        /\ \A lp \in SlushLoopProcess :
              \E t \in msgs : t.type = "term" /\ t.src = lp
        /\ pc' = [pc EXCEPT ![qp] = "Done"]
        /\ UNCHANGED <<color, msgs, sample, iter>>

\*=====================================================================
\*  Next-state relation
\*=====================================================================
Next ==
    \/ ClientAssign
    \/ LoopSample
    \/ LoopTally
    \/ LoopTerminate
    \/ QueryRespond
    \/ QueryTerminate

\*=====================================================================
\*  Specification
\*=====================================================================
Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iter>>

\*=====================================================================
\*  Type invariant
\*=====================================================================
TypeInvariant ==
    /\ color \in [Node -> Colors]
    /\ msgs \subseteq Message

====