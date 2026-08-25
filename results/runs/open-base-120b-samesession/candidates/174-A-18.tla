---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Node,                 \* set of all nodes
    SlushLoopProcess,     \* one loop process per node
    SlushQueryProcess,    \* one query process per node
    HostMapping,          \* set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,  \* number of iterations each loop process executes
    SampleSetSize,        \* size of the peer sample taken each iteration
    PickFlipThreshold,    \* threshold for adopting a color
    NoColor,              \* sentinel value meaning “uncolored”
    NoMessage             \* sentinel value for “no message” (unused but required)

\* ----------------------------------------------------------------------
\* Helper operators that extract the host node from the mapping
\* ----------------------------------------------------------------------
HostNodeOfLoop(lp) ==
    CHOOSE t \in HostMapping :
        /\ t[2] = lp
        /\ t[1] \in Node

HostNodeOfQuery(qp) ==
    CHOOSE t \in HostMapping :
        /\ t[3] = qp
        /\ t[1] \in Node

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    colors,   \* [Node -> {"Red","Blue"} \cup {NoColor}]
    msgs,     \* set of in‑flight messages
    sample,   \* [SlushLoopProcess -> SUBSET Node]   (peers sampled this round)
    iter      \* [SlushLoopProcess -> Nat]           (iterations already done)

\* ----------------------------------------------------------------------
\* Message definition (record)
\* ----------------------------------------------------------------------
Message ==
    [type : {"query","reply","term"},
     src  : (SlushLoopProcess \cup SlushQueryProcess),
     dst  : (SlushLoopProcess \cup SlushQueryProcess),
     color : {"Red","Blue"} \cup {NoColor}]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ colors = [n \in Node |-> NoColor]
    /\ msgs   = {}
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Action: Client assigns a random color to an uncolored node
\* ----------------------------------------------------------------------
ClientAssign ==
    \E n \in Node :
        /\ colors[n] = NoColor
        /\ \E c \in {"Red","Blue"} :
            /\ colors' = [colors EXCEPT ![n] = c]
            /\ UNCHANGED <<msgs, sample, iter>>

\* ----------------------------------------------------------------------
\* Action: A loop process performs one iteration (sampling, querying,
\*         tallying, possible flip, and bookkeeping)
\* ----------------------------------------------------------------------
LoopIter ==
    \E lp \in SlushLoopProcess :
        /\ iter[lp] < SlushIterationCount
        /\ LET hn == HostNodeOfLoop(lp) IN
           /\ colors[hn] # NoColor                     \* node already colored
           /\ \E s \subseteq Node \ {hn} :
                /\ Cardinality(s) = SampleSetSize
                /\ sample' = [sample EXCEPT ![lp] = s]
                /\ \* send a query to each sampled peer
                   msgsQ == { [type |-> "query",
                              src  |-> lp,
                              dst  |-> CHOOSE qp \in SlushQueryProcess :
                                         HostNodeOfQuery(qp) = peer,
                              color|-> colors[hn]] :
                              peer \in s }
                /\ msgs' = msgs \cup msgsQ
                /\ UNCHANGED <<colors, iter>>
        /\ \* Wait until all replies have arrived (modelled nondeterministically)
           \E replies \subseteq msgs :
                /\ \A m \in msgsQ :
                     /\ \E r \in msgs :
                          /\ r.type = "reply"
                          /\ r.dst = lp
                          /\ r.src = m.dst
                /\ \* Tally replies
                   reds  == Cardinality({ r \in replies :
                                          r.type = "reply" /\ r.dst = lp /\ r.color = "Red"})
                   blues == Cardinality({ r \in replies :
                                          r.type = "reply" /\ r.dst = lp /\ r.color = "Blue"})
                /\ \* Possibly flip the node's color
                   IF reds >= PickFlipThreshold
                      THEN colors'' = [colors EXCEPT ![hn] = "Red"]
                   ELSE IF blues >= PickFlipThreshold
                      THEN colors'' = [colors EXCEPT ![hn] = "Blue"]
                   ELSE colors'' = colors
                /\ \* Clean up messages from this round
                   msgs'' = msgs \ (msgsQ \cup replies)
                /\ colors' = colors''
                /\ msgs'   = msgs''
                /\ sample' = [sample EXCEPT ![lp] = {}]
                /\ iter'   = [iter EXCEPT ![lp] = @ + 1]
                /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Action: After completing all iterations a loop process broadcasts a termination
\* ----------------------------------------------------------------------
LoopTerminate ==
    \E lp \in SlushLoopProcess :
        /\ iter[lp] = SlushIterationCount
        /\ msgs' = msgs \cup
                   { [type |-> "term",
                      src  |-> lp,
                      dst  |-> qp,
                      color|-> NoColor] :
                      qp \in SlushQueryProcess }
        /\ UNCHANGED <<colors, sample, iter>>

\* ----------------------------------------------------------------------
\* Action: A query process reacts to an incoming query
\* ----------------------------------------------------------------------
QueryRespond ==
    \E qp \in SlushQueryProcess :
        /\ \E m \in msgs :
             /\ m.type = "query"
             /\ m.dst = qp
             /\ LET hn == HostNodeOfQuery(qp) IN
                /\ IF colors[hn] = NoColor
                      THEN colors' = [colors EXCEPT ![hn] = m.color]
                      ELSE colors' = colors
                /\ reply == [type  |-> "reply",
                             src   |-> qp,
                             dst   |-> m.src,
                             color |-> colors'[hn]]
                /\ msgs' = (msgs \ {m}) \cup {reply}
                /\ UNCHANGED <<sample, iter>>

\* ----------------------------------------------------------------------
\* Action: A query process terminates when it has received a termination
\*         message from every loop process
\* ----------------------------------------------------------------------
QueryTerminate ==
    \E qp \in SlushQueryProcess :
        /\ \A lp \in SlushLoopProcess :
              \E t \in msgs :
                  /\ t.type = "term"
                  /\ t.src = lp
                  /\ t.dst = qp
        /\ UNCHANGED <<colors, msgs, sample, iter>>

\* ----------------------------------------------------------------------
\* The global next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ ClientAssign
    \/ LoopIter
    \/ LoopTerminate
    \/ QueryRespond
    \/ QueryTerminate

\* ----------------------------------------------------------------------
\* Type invariant required by the .cfg file
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ colors \in [Node -> ({"Red","Blue"} \cup {NoColor})]
    /\ msgs \subseteq {
            [type : "query", src : SlushLoopProcess,  dst : SlushQueryProcess, color : {"Red","Blue"}],
            [type : "reply", src : SlushQueryProcess, dst : SlushLoopProcess,  color : {"Red","Blue"}],
            [type : "term",  src : SlushLoopProcess,  dst : SlushQueryProcess,  color : {NoColor}]
        }

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<colors, msgs, sample, iter>>

====