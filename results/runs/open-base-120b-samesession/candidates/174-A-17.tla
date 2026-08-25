---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Node,                \* the set of node identifiers
    SlushLoopProcess,    \* the set of loop process identifiers
    SlushQueryProcess,   \* the set of query process identifiers
    HostMapping,         \* set of triples <<node, loop, query>>
    SlushIterationCount, \* number of iterations each loop process must run
    SampleSetSize,       \* size of the random sample taken each round
    PickFlipThreshold,   \* threshold for adopting a color
    NoColor,             \* sentinel for “uncolored”
    NoMessage            \* sentinel for “no color” in termination messages

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue"}               \* the two possible colors

Message == [type : {"query", "reply", "term"},
            src  : (SlushLoopProcess \cup SlushQueryProcess),
            dst  : (SlushLoopProcess \cup SlushQueryProcess),
            col  : (Colors \cup {NoColor, NoMessage})]

HostNode(p) == CHOOSE t \in HostMapping : t[2] = p
HostNodeQ(q) == CHOOSE t \in HostMapping : t[3] = q

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    color,      \* [node -> (Colors \cup {NoColor})]
    msgs,       \* subset of Message
    sample,     \* [loopProc -> SUBSET Node]    (current sample set, empty when idle)
    tally,      \* [loopProc -> [c \in Colors |-> Nat]]  (counts of replies per color)
    iter,       \* [loopProc -> Nat]          (iterations completed)
    termSent,   \* SUBSET SlushLoopProcess   (loop processes that have sent termination)
    clientDone  \* BOOLEAN                    (TRUE when all nodes are colored)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ color    = [n \in Node |-> NoColor]
    /\ msgs     = {}
    /\ sample   = [p \in SlushLoopProcess |-> {}]
    /\ tally    = [p \in SlushLoopProcess |-> [c \in Colors |-> 0]]
    /\ iter     = [p \in SlushLoopProcess |-> 0]
    /\ termSent = {}
    /\ clientDone = FALSE

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------

(*--- Client assigns a random color to an uncolored node -------------------*)
ClientAssign ==
    /\ \E n \in Node : color[n] = NoColor
    /\ \E n \in Node :
          /\ color[n] = NoColor
          /\ c \in Colors
    /\ UNCHANGED <<sample, tally, iter, termSent, msgs>>
    /\ color' = [color EXCEPT ![n] = c]
    /\ clientDone' = IF \A n2 \in Node : color'[n2] # NoColor THEN TRUE ELSE FALSE

(*--- Loop process picks a random sample and sends query messages ---------*)
LoopSample ==
    /\ \E p \in SlushLoopProcess :
          /\ let n == HostNode(p) in
                /\ color[n] # NoColor
                /\ iter[p] < SlushIterationCount
                /\ sample[p] = {}
                /\ s \in SUBSET (Node \ {n})
                /\ Cardinality(s) = SampleSetSize
    /\ let p == CHOOSE p \in SlushLoopProcess :
                /\ let n == HostNode(p) IN
                   /\ color[n] # NoColor
                   /\ iter[p] < SlushIterationCount
                   /\ sample[p] = {}
                   /\ s \in SUBSET (Node \ {n})
                   /\ Cardinality(s) = SampleSetSize
          in
          sample' = [sample EXCEPT ![p] = s]  \* store the chosen sample
          /\ msgs' = msgs \cup {
                [type |-> "query",
                 src  |-> p,
                 dst  |-> q,
                 col  |-> color[HostNode(p)]]
                : q \in SlushQueryProcess :
                  HostNodeQ(q) \in s
             }
    /\ UNCHANGED <<color, tally, iter, termSent, clientDone>>

(*--- Query process receives a query, possibly adopts the color, replies ---*)
QueryRespond ==
    /\ \E m \in msgs :
         /\ m.type = "query"
         /\ q == m.dst
    /\ let q == CHOOSE q \in SlushQueryProcess :
               /\ \E m \in msgs :
                    /\ m.type = "query"
                    /\ m.dst = q
          in
          LET n == HostNodeQ(q) IN
              msgs' = msgs \ {m}
              /\ IF color[n] = NoColor
                 THEN color' = [color EXCEPT ![n] = m.col]
                 ELSE UNCHANGED color
              /\ msgs' = msgs' \cup {
                     [type |-> "reply",
                      src  |-> q,
                      dst  |-> m.src,
                      col  |-> color[n]]
                 }
    /\ UNCHANGED <<sample, tally, iter, termSent, clientDone>>

(*--- Loop process receives a reply and updates its tally ----------------*)
LoopReceiveReply ==
    /\ \E m \in msgs :
         /\ m.type = "reply"
         /\ p == m.dst
    /\ let p == CHOOSE p \in SlushLoopProcess :
               /\ \E m \in msgs :
                    /\ m.type = "reply"
                    /\ m.dst = p
          in
          LET c == m.col IN
              msgs'   = msgs \ {m}
              tally'  = [tally EXCEPT ![p][c] = @ + 1]
    /\ UNCHANGED <<color, sample, iter, termSent, clientDone>>

(*--- After all replies are in, possibly flip color and advance iteration --*)
LoopFlipOrAdvance ==
    /\ \E p \in SlushLoopProcess :
         /\ sample[p] # {}
         /\ \Sum_{c \in Colors} tally[p][c] = SampleSetSize
    /\ let p == CHOOSE p \in SlushLoopProcess :
                /\ sample[p] # {}
                /\ \Sum_{c \in Colors} tally[p][c] = SampleSetSize
          in
          LET n == HostNode(p) IN
          IF \E c \in Colors : tally[p][c] >= PickFlipThreshold
          THEN
              \E c \in Colors :
                 /\ tally[p][c] >= PickFlipThreshold
                 /\ color' = [color EXCEPT ![n] = c]
          ELSE
              UNCHANGED color
          /\ sample' = [sample EXCEPT ![p] = {}]
          /\ tally'  = [tally EXCEPT ![p] = [c \in Colors |-> 0]]
          /\ iter'   = [iter EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<msgs, termSent, clientDone>>

(*--- Loop process, after finishing all iterations, broadcasts termination -*)
LoopTerminate ==
    /\ \E p \in SlushLoopProcess :
         /\ iter[p] = SlushIterationCount
         /\ p \notin termSent
    /\ let p == CHOOSE p \in SlushLoopProcess :
                /\ iter[p] = SlushIterationCount
                /\ p \notin termSent
          in
          termSent' = termSent \cup {p}
          /\ msgs' = msgs \cup {
                [type |-> "term",
                 src  |-> p,
                 dst  |-> q,
                 col  |-> NoMessage]
                : q \in SlushQueryProcess
             }
    /\ UNCHANGED <<color, sample, tally, iter, clientDone>>

(*--- Gather all actions into Next ----------------------------------------*)
Next ==
    \/ ClientAssign
    \/ LoopSample
    \/ QueryRespond
    \/ LoopReceiveReply
    \/ LoopFlipOrAdvance
    \/ LoopTerminate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, sample, tally, iter, termSent, clientDone>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs \subseteq Message

====