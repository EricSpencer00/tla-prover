---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Node,                     \* set of all node identifiers
    SlushLoopProcess,         \* set of loop‑process identifiers (one per node)
    SlushQueryProcess,        \* set of query‑process identifiers (one per node)
    HostMapping,              \* set of records [node, loop, query] linking the three
    SlushIterationCount,      \* number of iterations each loop process must run
    SampleSetSize,            \* size of the random peer sample each round
    PickFlipThreshold,        \* minimum number of identical replies to flip colour
    NoColor,                  \* special value meaning “uncoloured”
    NoMessage                 \* placeholder for “no message”

(* --------------------------------------------------------------------- *)
(* Colours used by the protocol.                                         *)
Red  == "Red"
Blue == "Blue"

(* --------------------------------------------------------------------- *)
(* Helper functions that retrieve the node, its loop process, and its   *)
(* query process from the HostMapping.                                   *)
HostNode(l) == CHOOSE hm \in HostMapping : hm.loop = l .node
QueryProc(n) == CHOOSE hm \in HostMapping : hm.node = n .query

(* --------------------------------------------------------------------- *)
VARIABLES
    color,        \* [Node -> (Red \cup Blue \cup {NoColor})]
    msgs,         \* set of in‑flight messages
    sample,       \* [SlushLoopProcess -> SUBSET Node]   current sample set
    iter,         \* [SlushLoopProcess -> Nat]           iteration counter
    doneLoop,     \* set of loop processes that have terminated
    doneQuery     \* set of query processes that have terminated

vars == <<color, msgs, sample, iter, doneLoop, doneQuery>>

(* --------------------------------------------------------------------- *)
Init ==
    /\ color   = [n \in Node |-> NoColor]
    /\ msgs    = {}
    /\ sample  = [l \in SlushLoopProcess |-> {}]
    /\ iter    = [l \in SlushLoopProcess |-> 0]
    /\ doneLoop = {}
    /\ doneQuery = {}

(* --------------------------------------------------------------------- *)
(* 1. The client assigns a colour to an uncoloured node.                 *)
ClientAssign ==
    \E n \in Node :
        /\ color[n] = NoColor
        /\ \/ color' = [color EXCEPT ![n] = Red]
           \/ color' = [color EXCEPT ![n] = Blue]
        /\ UNCHANGED <<msgs, sample, iter, doneLoop, doneQuery>>

(* --------------------------------------------------------------------- *)
(* 2. A loop process samples peers and sends query messages.            *)
LoopSample ==
    \E l \in SlushLoopProcess :
        LET n == HostNode(l) IN
        /\ iter[l] < SlushIterationCount
        /\ sample[l] = {}
        /\ \E s \subseteq Node \ {n} :
               Cardinality(s) = SampleSetSize
        /\ sample' = [sample EXCEPT ![l] = s]
        /\ msgs' = msgs \cup
              { [type |-> "query",
                 src  |-> l,
                 dst  |-> QueryProc(m),
                 col  |-> color[n]] : m \in s }
        /\ UNCHANGED <<color, iter, doneLoop, doneQuery>>

(* --------------------------------------------------------------------- *)
(* 3. A query process reacts to a query, possibly adopting the colour   *)
(*    and always replying.                                               *)
QueryRespond ==
    \E q \in SlushQueryProcess :
        \E m \in msgs :
            /\ m.type = "query"
            /\ m.dst = q
            LET n == (CHOOSE hm \in HostMapping : hm.query = q).node IN
            /\ IF color[n] = NoColor
               THEN color' = [color EXCEPT ![n] = m.col]
               ELSE color' = color
            /\ msgs' = (msgs \ {m}) \cup
                 { [type |-> "reply",
                    src  |-> q,
                    dst  |-> m.src,
                    col  |-> color'[n]] }
            /\ UNCHANGED <<sample, iter, doneLoop, doneQuery>>

(* --------------------------------------------------------------------- *)
(* 4. A loop process tallies the replies, possibly flipping its colour, *)
(*    clears its sample set and increments its iteration counter.      *)
LoopTally ==
    \E l \in SlushLoopProcess :
        LET n == HostNode(l) IN
        LET s == sample[l] IN
        /\ s # {}
        /\ \A m \in s :
              \E rep \in msgs :
                 rep.type = "reply"
                 /\ rep.src = QueryProc(m)
                 /\ rep.dst = l
        /\ LET reds  == { m \in s :
                \E rep \in msgs :
                   rep.type = "reply"
                   /\ rep.src = QueryProc(m)
                   /\ rep.dst = l
                   /\ rep.col = Red } IN
           blues == { m \in s :
                \E rep \in msgs :
                   rep.type = "reply"
                   /\ rep.src = QueryProc(m)
                   /\ rep.dst = l
                   /\ rep.col = Blue } IN
        /\ color' = IF Cardinality(reds) >= PickFlipThreshold
                     THEN [color EXCEPT ![n] = Red]
                     ELSE IF Cardinality(blues) >= PickFlipThreshold
                          THEN [color EXCEPT ![n] = Blue]
                          ELSE color
        /\ msgs'   = msgs \ { rep \in msgs :
                rep.type = "reply" /\ rep.dst = l }
        /\ sample' = [sample EXCEPT ![l] = {}]
        /\ iter'   = [iter EXCEPT ![l] = @ + 1]
        /\ UNCHANGED <<doneLoop, doneQuery>>

(* --------------------------------------------------------------------- *)
(* 5. After finishing all iterations a loop process broadcasts a       *)
(*    termination message and records that it is done.                  *)
LoopTerminate ==
    \E l \in SlushLoopProcess :
        /\ iter[l] = SlushIterationCount
        /\ doneLoop' = doneLoop \cup {l}
        /\ msgs' = msgs \cup
              { [type |-> "term",
                 src  |-> l,
                 dst  |-> q,
                 col  |-> NoColor] : q \in SlushQueryProcess }
        /\ UNCHANGED <<color, sample, iter, doneQuery>>

(* --------------------------------------------------------------------- *)
(* 6. A query process exits once it has received a termination from    *)
(*    every loop process.                                                *)
QueryExit ==
    \E q \in SlushQueryProcess :
        /\ \A l \in SlushLoopProcess :
               \E t \in msgs :
                  t.type = "term" /\ t.src = l /\ t.dst = q
        /\ doneQuery' = doneQuery \cup {q}
        /\ msgs' = msgs \ { t \in msgs :
               t.type = "term" /\ t.dst = q }
        /\ UNCHANGED <<color, sample, iter, doneLoop>>

(* --------------------------------------------------------------------- *)
Next ==
    \/ ClientAssign
    \/ LoopSample
    \/ QueryRespond
    \/ LoopTally
    \/ LoopTerminate
    \/ QueryExit

Spec == Init /\ [][Next]_vars

(* --------------------------------------------------------------------- *)
(* Type safety invariant.                                                *)
TypeInvariant ==
    /\ color \in [Node -> (Red \cup Blue \cup {NoColor})]
    /\ msgs \subseteq
        [type : {"query","reply","term"},
         src  : (SlushLoopProcess \cup SlushQueryProcess),
         dst  : (SlushLoopProcess \cup SlushQueryProcess),
         col  : (Red \cup Blue \cup {NoColor})]

====