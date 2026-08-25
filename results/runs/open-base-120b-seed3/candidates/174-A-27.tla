---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Node,
    SlushLoopProcess,
    SlushQueryProcess,
    HostMapping,
    SlushIterationCount,
    SampleSetSize,
    PickFlipThreshold,
    NoColor,
    NoMessage

(* ----------------------------------------------------------------------
   The two possible colors (the protocol works with any two distinct values)
   ---------------------------------------------------------------------- *)
CONSTANTS Colors
ASSUME Colors = {"Red", "Blue"}

(* ----------------------------------------------------------------------
   Message record definition
   ---------------------------------------------------------------------- *)
Message == [type : {"query", "reply", "term"},
            src  : Node,
            dst  : Node,
            col  : (Colors \cup {NoColor, NoMessage})]

VARIABLES
    color,   \* [Node -> (Colors \cup {NoColor})]
    msgs,    \* set of Message
    sample,  \* [Node -> SUBSET Node]  current sample set for each node
    iter,    \* [Node -> Nat]           iteration counter per node
    done     \* SUBSET Node             nodes that have finished all iterations

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ sample = [n \in Node |-> {}]
    /\ iter   = [n \in Node |-> 0]
    /\ done   = {}

(* ----------------------------------------------------------------------
   1. Client assigns a random color to an uncolored node
   ---------------------------------------------------------------------- *)
ClientAssign ==
    /\ \E n \in Node : color[n] = NoColor
    /\ LET n == CHOOSE n \in Node : color[n] = NoColor
           c == CHOOSE c \in Colors
       IN  color' = [color EXCEPT ![n] = c]
    /\ UNCHANGED <<msgs, sample, iter, done>>

(* ----------------------------------------------------------------------
   2. A loop process starts a new iteration (samples peers and sends queries)
   ---------------------------------------------------------------------- *)
StartIteration ==
    /\ \E n \in Node :
          /\ color[n] # NoColor
          /\ iter[n] < SlushIterationCount
          /\ sample[n] = {}
    /\ LET n == CHOOSE n \in Node :
           /\ color[n] # NoColor
           /\ iter[n] < SlushIterationCount
           /\ sample[n] = {}
           S == CHOOSE S \subseteq Node \ {n} :
                 Cardinality(S) = SampleSetSize
       IN  /\ sample' = [sample EXCEPT ![n] = S]
           /\ msgs' = msgs \cup
               { [type |-> "query",
                  src  |-> n,
                  dst  |-> m,
                  col  |-> color[n]] : m \in S }
           /\ UNCHANGED <<color, iter, done>>

(* ----------------------------------------------------------------------
   3. A query process receives a query (modeled as the node itself)
   ---------------------------------------------------------------------- *)
ReceiveQuery ==
    /\ \E m \in msgs :
          /\ m.type = "query"
    /\ LET q == CHOOSE m \in msgs : m.type = "query"
       IN  LET n  == q.dst
               src == q.src
               incCol == q.col
               newCol == IF color[n] = NoColor THEN incCol ELSE color[n]
           IN  /\ color' = [color EXCEPT ![n] = newCol]
               /\ msgs' = (msgs \ {q}) \cup
                    { [type |-> "reply",
                       src  |-> n,
                       dst  |-> src,
                       col  |-> newCol] }
               /\ UNCHANGED <<sample, iter, done>>

(* ----------------------------------------------------------------------
   4. Tally replies once all sampled peers have replied
   ---------------------------------------------------------------------- *)
TallyReplies ==
    /\ \E n \in Node :
          /\ sample[n] # {}
          /\ \A p \in sample[n] :
                \E r \in msgs :
                    /\ r.type = "reply"
                    /\ r.dst = n
                    /\ r.src = p
    /\ LET n == CHOOSE n \in Node :
           /\ sample[n] # {}
           /\ \A p \in sample[n] :
                \E r \in msgs :
                    /\ r.type = "reply"
                    /\ r.dst = n
                    /\ r.src = p
           redCnt  == Cardinality({ r \in msgs :
                                    r.type = "reply" /\ r.dst = n /\ r.col = "Red" })
           blueCnt == Cardinality({ r \in msgs :
                                    r.type = "reply" /\ r.dst = n /\ r.col = "Blue" })
           newCol  == IF redCnt >= PickFlipThreshold THEN "Red"
                     ELSE IF blueCnt >= PickFlipThreshold THEN "Blue"
                     ELSE color[n]
       IN  /\ color' = [color EXCEPT ![n] = newCol]
           /\ sample' = [sample EXCEPT ![n] = {}]
           /\ iter'   = [iter EXCEPT ![n] = @ + 1]
           /\ done'   = IF iter'[n] = SlushIterationCount
                         THEN done \cup {n}
                         ELSE done
           /\ msgs'   = msgs \ { r \in msgs :
                                 r.type = "reply" /\ r.dst = n /\ r.src \in sample[n] }
           /\ UNCHANGED <<>>

(* ----------------------------------------------------------------------
   5. Termination: when all nodes have finished their iterations
   ---------------------------------------------------------------------- *)
Terminate ==
    /\ done = Node
    /\ UNCHANGED <<color, msgs, sample, iter, done>>

Next ==
    \/ ClientAssign
    \/ StartIteration
    \/ ReceiveQuery
    \/ TallyReplies
    \/ Terminate

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<color, msgs, sample, iter, done>>

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)
TypeInvariant ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs \subseteq Message

====