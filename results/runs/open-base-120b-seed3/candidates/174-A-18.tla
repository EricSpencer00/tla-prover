---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

\*--------------------------------------------------------------------
\* CONSTANTS (to be instantiated in the .cfg file)
\*--------------------------------------------------------------------
CONSTANTS 
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* Set of loop process identifiers (one per node)
    SlushQueryProcess,  \* Set of query process identifiers (one per node)
    HostMapping,        \* Set of triples <<node, loopProc, queryProc>>
    SlushIterationCount,\* Number of iterations each loop process performs
    SampleSetSize,      \* Size of the peer sample taken each round
    PickFlipThreshold,  \* Minimum number of matching replies to trigger a flip
    NoColor,            \* Symbol for an uncolored node
    NoMessage           \* Symbol for the absence of a message (unused but required)

\*--------------------------------------------------------------------
\* Derived sets and helper functions
\*--------------------------------------------------------------------
Process == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

Colors == {"Red", "Blue"}

Message == [type   : {"query", "reply", "term"},
            src    : Process,
            dst    : Process,
            color  : Colors \cup {NoColor}]

\* Given a loop process, return its host node
LoopNode(l) == 
    CHOOSE n \in Node :
        \E q \in SlushQueryProcess : <<n, l, q>> \in HostMapping

\* Given a query process, return its host node
QueryNode(q) == 
    CHOOSE n \in Node :
        \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping

\* Given a node, return its associated query process
QueryProc(n) == 
    CHOOSE q \in SlushQueryProcess :
        \E l \in SlushLoopProcess : <<n, l, q>> \in HostMapping

\*--------------------------------------------------------------------
\* VARIABLES
\*--------------------------------------------------------------------
VARIABLES 
    color,        \* [node -> (Colors \cup {NoColor})]
    msgs,         \* Set of in‑flight Message records
    pc,           \* [process -> state]
    sampleSet,    \* [loopProc -> SUBSET Node]   (current peer sample)
    iter          \* [loopProc -> Nat]          (iterations completed)

\*--------------------------------------------------------------------
\* State predicates
\*--------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ pc = [p \in Process |-> 
                IF p = "Client" THEN "ClientAssign"
                ELSE IF p \in SlushLoopProcess THEN "LoopWait"
                ELSE "QueryReplyLoop"]
    /\ sampleSet = [l \in SlushLoopProcess |-> {}]
    /\ iter = [l \in SlushLoopProcess |-> 0]

\*--------------------------------------------------------------------
\* Actions
\*--------------------------------------------------------------------
ClientAssign ==
    /\ pc["Client"] = "ClientAssign"
    /\ \E n \in Node : color[n] = NoColor
    /\ \E c \in Colors :
        /\ color' = [color EXCEPT ![n] = c]
        /\ UNCHANGED <<msgs, pc, sampleSet, iter>>
        /\ pc' = [pc EXCEPT !["Client"] = "ClientAssign"]

ClientDone ==
    /\ pc["Client"] = "ClientAssign"
    /\ \A n \in Node : color[n] # NoColor
    /\ pc' = [pc EXCEPT !["Client"] = "Done"]
    /\ UNCHANGED <<color, msgs, sampleSet, iter>>

LoopWait ==
    /\ \E l \in SlushLoopProcess :
        /\ pc[l] = "LoopWait"
        /\ LET n == LoopNode(l) IN color[n] # NoColor
        /\ pc' = [pc EXCEPT ![l] = "LoopSample"]
        /\ UNCHANGED <<color, msgs, sampleSet, iter>>

LoopSample ==
    /\ \E l \in SlushLoopProcess :
        /\ pc[l] = "LoopSample"
        /\ LET n == LoopNode(l) IN
            /\ \E s \subseteq Node \ {n} :
                /\ Cardinality(s) = SampleSetSize
                /\ sampleSet' = [sampleSet EXCEPT ![l] = s]
                /\ msgs' = msgs \cup 
                    { [type  |-> "query",
                       src   |-> l,
                       dst   |-> QueryProc(n'),
                       color |-> color[n]] : n' \in s }
                /\ pc' = [pc EXCEPT ![l] = "LoopTally"]
                /\ UNCHANGED <<color, iter>>
        /\ UNCHANGED <<sampleSet, iter>>   \* (overridden by the inner definition)

RespondQuery ==
    /\ \E q \in SlushQueryProcess :
        /\ pc[q] = "QueryReplyLoop"
        /\ \E m \in msgs :
            /\ m.type = "query" /\ m.dst = q
            LET n == QueryNode(q) IN
                /\ color' = IF color[n] = NoColor
                              THEN [color EXCEPT ![n] = m.color]
                              ELSE color
                /\ reply == [type  |-> "reply",
                             src   |-> q,
                             dst   |-> m.src,
                             color |-> color'[n]]
                /\ msgs' = (msgs \ {m}) \cup {reply}
                /\ pc' = [pc EXCEPT ![q] = "QueryReplyLoop"]
                /\ UNCHANGED <<sampleSet, iter>>

LoopTally ==
    /\ \E l \in SlushLoopProcess :
        /\ pc[l] = "LoopTally"
        /\ LET n  == LoopNode(l)
               s  == sampleSet[l] IN
            /\ \A n' \in s :
                 \E r \in msgs :
                     /\ r.type = "reply"
                     /\ r.dst  = l
                     /\ r.src  = QueryProc(n')
            /\ reds  == { r \in msgs : r.type = "reply" /\ r.dst = l /\ r.color = "Red" }
            /\ blues == { r \in msgs : r.type = "reply" /\ r.dst = l /\ r.color = "Blue" }
            /\ newCol == 
                 IF Cardinality(reds) >= PickFlipThreshold THEN "Red"
                 ELSE IF Cardinality(blues) >= PickFlipThreshold THEN "Blue"
                 ELSE color[n]
            /\ color' = [color EXCEPT ![n] = newCol]
            /\ msgs' = msgs \ { r \in msgs : r.type = "reply" /\ r.dst = l }
            /\ iter' = [iter EXCEPT ![l] = @ + 1]
            /\ sampleSet' = [sampleSet EXCEPT ![l] = {}]
            /\ IF iter'[l] >= SlushIterationCount
               THEN pc' = [pc EXCEPT ![l] = "LoopTerminate"]
               ELSE pc' = [pc EXCEPT ![l] = "LoopSample"]
            /\ UNCHANGED <<pc>>   \* (pc' already defined)
        /\ UNCHANGED <<sampleSet, iter>>   \* (overridden inside)

LoopTerminate ==
    /\ \E l \in SlushLoopProcess :
        /\ pc[l] = "LoopTerminate"
        /\ msgs' = msgs \cup 
            { [type |-> "term",
               src  |-> l,
               dst  |-> q,
               color|-> NoColor] : q \in SlushQueryProcess }
        /\ pc' = [pc EXCEPT ![l] = "Done"]
        /\ UNCHANGED <<color, sampleSet, iter>>

QueryExit ==
    /\ \E q \in SlushQueryProcess :
        /\ pc[q] = "QueryReplyLoop"
        /\ \A l \in SlushLoopProcess :
             \E m \in msgs :
                 /\ m.type = "term"
                 /\ m.src = l
                 /\ m.dst = q
        /\ pc' = [pc EXCEPT ![q] = "Done"]
        /\ UNCHANGED <<color, msgs, sampleSet, iter>>

\* Processes that are already done simply stay unchanged
Stutter ==
    /\ UNCHANGED <<color, msgs, pc, sampleSet, iter>>

Next == 
    \/ ClientAssign
    \/ ClientDone
    \/ LoopWait
    \/ LoopSample
    \/ RespondQuery
    \/ LoopTally
    \/ LoopTerminate
    \/ QueryExit
    \/ Stutter

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, pc, sampleSet, iter>>

\*--------------------------------------------------------------------
\* Type invariant
\*--------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs \subseteq Message
    /\ pc \in [Process -> {"ClientAssign","LoopWait","LoopSample",
                          "LoopTally","LoopTerminate",
                          "QueryReplyLoop","Done"}]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET Node]
    /\ iter \in [SlushLoopProcess -> Nat]

\*--------------------------------------------------------------------
\* End of module
\*--------------------------------------------------------------------
====