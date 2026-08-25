---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(*  Constants required by the .cfg file                                    *)
(***************************************************************************)
CONSTANTS 
    Node,                \* The set of all node identifiers
    SlushLoopProcess,    \* One loop process per node
    SlushQueryProcess,   \* One query process per node
    HostMapping,         \* Set of triples <<node, loopProc, queryProc>>
    SlushIterationCount, \* Number of iterations each loop process runs
    SampleSetSize,       \* Size of the peer sample taken each round
    PickFlipThreshold,   \* Minimum number of equal replies to trigger a flip
    NoColor,             \* Value denoting an uncolored node
    NoMessage             \* Value denoting the absence of a message

(***************************************************************************)
(*  Derived sets and helper functions                                      *)
(***************************************************************************)
Colors == {"Red", "Blue", NoColor}

Message == 
    [type : {"query", "reply", "term"},
     src  : (SlushLoopProcess \cup SlushQueryProcess),
     dst  : (SlushLoopProcess \cup SlushQueryProcess),
     col  : Colors]

\* Functions that extract the node associated with a loop or a query process.
NodeOfLoop(p) == 
    CHOOSE n \in Node :
        \E q \in SlushQueryProcess : <<n, p, q>> \in HostMapping

NodeOfQuery(q) == 
    CHOOSE n \in Node :
        \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping

(***************************************************************************)
(*  Variables                                                              *)
(***************************************************************************)
VARIABLES 
    color,   \* [node \in Node |-> Colors]   current color of each node
    msgs,    \* set of in‑flight Message records
    sample,  \* [loopProc \in SlushLoopProcess |-> SUBSET SlushQueryProcess] current sample set
    iter,    \* [loopProc \in SlushLoopProcess |-> Nat]   number of completed iterations
    pc       \* [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> STRING] program counter (for readability)

(***************************************************************************)
(*  Initial state                                                          *)
(***************************************************************************)
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ sample = [p \in SlushLoopProcess |-> {}]
    /\ iter   = [p \in SlushLoopProcess |-> 0]
    /\ pc     = [proc \in (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) |-> "init"]

(***************************************************************************)
(*  Actions                                                               *)
(***************************************************************************)

\* --- Client: assign a random color to an uncolored node -----------------
ClientAssign ==
    /\ \E n \in Node : color[n] = NoColor
    /\ \E col \in {"Red","Blue"} :
        /\ color' = [color EXCEPT ![n] = col]
        /\ UNCHANGED <<msgs, sample, iter, pc>>

\* --- Loop processes ------------------------------------------------------
RequireColor(p) ==
    /\ color[NodeOfLoop(p)] # NoColor
    /\ UNCHANGED <<color, msgs, sample, iter, pc>>

SelectSample(p) ==
    /\ iter[p] < SlushIterationCount
    /\ sample[p] = {}
    /\ LET candidates == { q \in SlushQueryProcess : q # NodeOfQuery(NodeOfLoop(p)) } IN
       /\ sample' = [sample EXCEPT ![p] = 
                        CHOOSE s \subseteq candidates : Cardinality(s) = SampleSetSize]
    /\ UNCHANGED <<color, msgs, iter, pc>>

SendQueries(p) ==
    /\ sample[p] # {}
    /\ msgs' = msgs \cup 
        { [type |-> "query",
           src  |-> p,
           dst  |-> q,
           col  |-> color[NodeOfLoop(p)]] : q \in sample[p] }
    /\ UNCHANGED <<color, sample, iter, pc>>

ReceiveReplies(p) ==
    /\ sample[p] # {}
    /\ \A q \in sample[p] :
         \E m \in msgs : /\ m.type = "reply"
                         /\ m.src  = q
                         /\ m.dst  = p
    /\ UNCHANGED <<color, msgs, sample, iter, pc>>

FlipColor(p) ==
    /\ sample[p] # {}
    /\ LET replies == { m \in msgs : m.type = "reply" /\ m.dst = p } IN
       LET redCnt  == Cardinality({ r \in replies : r.col = "Red" })
           blueCnt == Cardinality({ r \in replies : r.col = "Blue" }) IN
          IF redCnt >= PickFlipThreshold THEN
              color' = [color EXCEPT ![NodeOfLoop(p)] = "Red"]
          ELSE IF blueCnt >= PickFlipThreshold THEN
              color' = [color EXCEPT ![NodeOfLoop(p)] = "Blue"]
          ELSE
              color' = color
          END IF
    /\ sample' = [sample EXCEPT ![p] = {}]
    /\ iter'   = [iter   EXCEPT ![p] = @ + 1]
    /\ UNCHANGED msgs
    /\ UNCHANGED pc

TerminateLoop(p) ==
    /\ iter[p] = SlushIterationCount
    /\ msgs' = msgs \cup 
        { [type |-> "term",
           src  |-> p,
           dst  |-> p,
           col  |-> NoColor] }
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<color, sample, iter>>

\* --- Query processes ------------------------------------------------------
QueryRespond(q) ==
    /\ \E m \in msgs : m.type = "query" /\ m.dst = q
    /\ LET m == CHOOSE mm \in msgs : mm.type = "query" /\ mm.dst = q IN
       /\ IF color[NodeOfQuery(q)] = NoColor THEN
              color' = [color EXCEPT ![NodeOfQuery(q)] = m.col]
          ELSE
              UNCHANGED color
          END IF
    /\ msgs' = msgs \cup 
        { [type |-> "reply",
           src  |-> q,
           dst  |-> m.src,
           col  |-> color[NodeOfQuery(q)]] }
    /\ UNCHANGED <<sample, iter, pc>>

QueryTerminate(q) ==
    /\ \A p \in SlushLoopProcess :
          \E t \in msgs : t.type = "term" /\ t.dst = p
    /\ pc' = [pc EXCEPT ![q] = "done"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

(***************************************************************************)
(*  Next-state relation                                                    *)
(***************************************************************************)
Next ==
    \/ \E n \in Node : ClientAssign
    \/ \E p \in SlushLoopProcess : RequireColor(p)
    \/ \E p \in SlushLoopProcess : SelectSample(p)
    \/ \E p \in SlushLoopProcess : SendQueries(p)
    \/ \E p \in SlushLoopProcess : ReceiveReplies(p)
    \/ \E p \in SlushLoopProcess : FlipColor(p)
    \/ \E p \in SlushLoopProcess : TerminateLoop(p)
    \/ \E q \in SlushQueryProcess : QueryRespond(q)
    \/ \E q \in SlushQueryProcess : QueryTerminate(q)

(***************************************************************************)
(*  Specification                                                          *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<color, msgs, sample, iter, pc>>

(***************************************************************************)
(*  Type invariant                                                         *)
(***************************************************************************)
TypeInvariant ==
    /\ color \in [Node -> Colors]
    /\ msgs \subseteq Message
    /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iter \in [SlushLoopProcess -> Nat]
    /\ pc \in [ (SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}) -> STRING]

=============================================================================