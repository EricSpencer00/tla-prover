---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Node,                     \* set of node identifiers
    SlushLoopProcess,         \* set of loop process identifiers
    SlushQueryProcess,        \* set of query process identifiers
    HostMapping,              \* set of triples <<loopProc, queryProc, node>>
    SlushIterationCount,      \* number of iterations each loop process performs
    SampleSetSize,            \* size of the peer sample per iteration
    PickFlipThreshold,        \* threshold for adopting a color
    NoColor,                  \* special value denoting “uncolored”
    NoMessage                 \* placeholder for “no message”

(*--------------------------------------------------------------------
  Derived collections
--------------------------------------------------------------------*)
LoopProc == SlushLoopProcess
QueryProc == SlushQueryProcess

Color == {"Red", "Blue"}          \* the two possible colors

Message ==
    UNION {
        [type : "query", src : LoopProc, dst : QueryProc, col : Color \/ {NoColor}],
        [type : "reply", src : QueryProc, dst : LoopProc, col : Color \/ {NoColor}],
        [type : "term",  src : LoopProc, dst : QueryProc]
    }

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    color,          \* [node -> Color \/ {NoColor}]
    msgs,           \* subset of Message
    pc,             \* [proc -> string]   program counter per process
    sample,         \* [loopProc -> SUBSET QueryProc]  current sample set
    iter,           \* [loopProc -> Nat]  number of completed iterations
    termCount       \* Nat  number of termination messages sent

(*--------------------------------------------------------------------
  Helper functions
--------------------------------------------------------------------*)
NodeOfQuery(q) == 
    CHOOSE n \in Node : <<_, q, n>> \in HostMapping

NodeOfLoop(p) ==
    CHOOSE n \in Node : <<p, _, n>> \in HostMapping

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [p \in LoopProc \cup QueryProc \cup {"client"} |-> "Init"]
    /\ sample = [p \in LoopProc |-> {}]
    /\ iter = [p \in LoopProc |-> 0]
    /\ termCount = 0

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
ClientAssign ==
    /\ pc["client"] = "Init"
    /\ \E n \in Node :
          /\ color[n] = NoColor
          /\ \E c \in Color :
                /\ color' = [color EXCEPT ![n] = c]
                /\ UNCHANGED <<msgs, pc, sample, iter, termCount>>
    /\ pc' = [pc EXCEPT !["client"] = "Done"]
    \/ (* all nodes already colored *)
      /\ \A n \in Node : color[n] # NoColor
      /\ pc' = [pc EXCEPT !["client"] = "Done"]
      /\ UNCHANGED <<color, msgs, sample, iter, termCount>>

LoopRequireColor(p) ==
    /\ p \in LoopProc
    /\ pc[p] = "Init"
    /\ \E n \in Node :
          <<p, _, n>> \in HostMapping /\ color[n] # NoColor
    /\ pc' = [pc EXCEPT ![p] = "Sample"]
    /\ UNCHANGED <<color, msgs, sample, iter, termCount>>

LoopSendQueries(p) ==
    /\ p \in LoopProc
    /\ pc[p] = "Sample"
    /\ LET allPeers == { q \in QueryProc :
            \E n_q \in Node :
                <<p, q, n_q>> \in HostMapping /\ n_q # NodeOfLoop(p) } 
       IN
       /\ sample' = [sample EXCEPT ![p] = 
               CHOOSE s \in SUBSET allPeers : Cardinality(s) = SampleSetSize]
    /\ msgs' = msgs \cup
          { [type |-> "query",
             src  |-> p,
             dst  |-> q,
             col  |-> color[NodeOfLoop(p)] ] :
                q \in sample'[p] }
    /\ pc' = [pc EXCEPT ![p] = "WaitReplies"]
    /\ UNCHANGED <<color, iter, termCount>>

QueryRespond ==
    /\ \E m \in msgs :
          /\ m.type = "query"
    /\ LET q == m.dst IN
          /\ LET n == NodeOfQuery(q) IN
          /\ LET adopt ==
                IF color[n] = NoColor THEN m.col ELSE color[n] END
          IN
          /\ msgs' = (msgs \ {m}) \cup
                { [type |-> "reply",
                   src  |-> q,
                   dst  |-> m.src,
                   col  |-> adopt] }
          /\ IF color[n] = NoColor
                THEN color' = [color EXCEPT ![n] = m.col]
                ELSE color' = color
          /\ UNCHANGED <<sample, iter, termCount>>
          /\ pc' = pc   \* query processes stay in the same pc state

LoopTally(p) ==
    /\ p \in LoopProc
    /\ pc[p] = "WaitReplies"
    /\ \A r \in msgs :
          (r.type = "reply" /\ r.dst = p) => r.src \in sample[p]
    /\ LET replies == { r \in msgs :
                         r.type = "reply" /\ r.dst = p } IN
       LET reds   == Cardinality({ r \in replies : r.col = "Red" }) IN
       LET blues  == Cardinality({ r \in replies : r.col = "Blue" }) IN
       LET curNode == NodeOfLoop(p) IN
       LET curCol  == color[curNode] IN
       LET newCol ==
            IF reds >= PickFlipThreshold THEN "Red"
            ELSE IF blues >= PickFlipThreshold THEN "Blue"
            ELSE curCol
       IN
       /\ color' = [color EXCEPT ![curNode] = newCol]
       /\ msgs' = msgs \ { r \in msgs : r.type = "reply" /\ r.dst = p }
       /\ iter' = [iter EXCEPT ![p] = @ + 1]
       /\ IF iter'[p] = SlushIterationCount
            THEN pc' = [pc EXCEPT ![p] = "Terminate"]
            ELSE pc' = [pc EXCEPT ![p] = "Sample"]
       /\ sample' = [sample EXCEPT ![p] = {}]
       /\ UNCHANGED termCount

LoopTerminate(p) ==
    /\ p \in LoopProc
    /\ pc[p] = "Terminate"
    /\ msgs' = msgs \cup
          { [type |-> "term", src |-> p, dst |-> q] :
                q \in QueryProc }
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ termCount' = termCount + 1
    /\ UNCHANGED <<color, sample, iter>>

QueryExit ==
    /\ \E q \in QueryProc :
          pc[q] # "Done" /\ termCount = Cardinality(LoopProc)
    /\ pc' = [pc EXCEPT ![q] = "Done"]
    /\ UNCHANGED <<color, msgs, sample, iter, termCount>>

Next ==
    \/ ClientAssign
    \/ \E p \in LoopProc : LoopRequireColor(p)
    \/ \E p \in LoopProc : LoopSendQueries(p)
    \/ QueryRespond
    \/ \E p \in LoopProc : LoopTally(p)
    \/ \E p \in LoopProc : LoopTerminate(p)
    \/ QueryExit

(*--------------------------------------------------------------------
  Specification and invariants
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iter, termCount>>

TypeInvariant ==
    /\ color \in [Node -> (Color \/ {NoColor})]
    /\ msgs \subseteq Message

====