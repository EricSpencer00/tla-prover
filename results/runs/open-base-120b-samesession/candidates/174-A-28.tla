---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Node,                     \* Set of node identifiers
    SlushLoopProcess,         \* Set of loop process identifiers
    SlushQueryProcess,        \* Set of query process identifiers
    HostMapping,              \* Set of triples <<proc, node, role>>
    SlushIterationCount,      \* Number of iterations each loop process must perform
    SampleSetSize,            \* Size of the peer sample taken each round
    PickFlipThreshold,        \* Minimum number of equal‑colored replies needed to flip
    NoColor,                  \* Special value meaning “uncolored”
    NoMessage                 \* Special value for “no message” (unused but required)

\* ----------------------------------------------------------------------
\* Derived sets and functions
\* ----------------------------------------------------------------------
Colors == {"Red", "Blue"}                       \* The two possible colors

Process == SlushLoopProcess \cup SlushQueryProcess \cup {"Client"}

\* Host functions extracted from the HostMapping constant.
\* Each mapping triple is of the form <<proc, node, role>> where
\*   role = "loop" for loop processes and "query" for query processes.
LoopHost(p) == CHOOSE n \in Node : <<p, n, "loop">> \in HostMapping
QueryHost(p) == CHOOSE n \in Node : <<p, n, "query">> \in HostMapping

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Message ==
    [type   : {"query", "reply", "term"},
     from   : Process,
     to     : Process,
     color  : Colors \cup {NoColor}]   \* “color” is irrelevant for termination msgs

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    color,      \* [Node -> (Colors \cup {NoColor})] current node colors
    msgs,       \* Set of in‑flight messages
    pc,         \* [Process -> PC] program counter for each process
    sample,     \* [SlushLoopProcess -> SUBSET SlushQueryProcess] current peer sample
    iter        \* [SlushLoopProcess -> Nat] number of completed iterations

\* ----------------------------------------------------------------------
\* Program‑counter values
\* ----------------------------------------------------------------------
PCValues ==
    {"client",                \* client process ready to assign a color
     "waitColor",             \* loop process waiting for its node to be colored
     "sample",                \* loop process selecting peers
     "collect",               \* loop process waiting for replies
     "done",                  \* loop process finished all iterations
     "reply",                 \* query process ready to answer queries
     "queryDone"}             \* query process finished (all loops terminated)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
UncoloredNodes == {n \in Node : color[n] = NoColor}
AllLoopsDone == \A lp \in SlushLoopProcess : pc[lp] = "done"

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ color = [n \in Node |-> NoColor]
    /\ msgs  = {}
    /\ pc    = [p \in Process |
                IF p = "Client" THEN "client"
                ELSE IF p \in SlushLoopProcess THEN "waitColor"
                ELSE "reply"]
    /\ sample = [lp \in SlushLoopProcess |-> {}]
    /\ iter   = [lp \in SlushLoopProcess |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
(* --algorithm SlushAlg
variables
    color = [n \in Node |-> NoColor],
    msgs  = {},
    pc    = [p \in Process |
                if p = "Client" then "client"
                else if p \in SlushLoopProcess then "waitColor"
                else "reply"],
    sample = [lp \in SlushLoopProcess |-> {}],
    iter   = [lp \in SlushLoopProcess |-> 0];

process (Client = "Client")
begin
ClientStep:
    while TRUE do
        either
            /\ UNCHANGED <<color, msgs, pc, sample, iter>>
        or
            /\ \E n \in UncoloredNodes :
               LET col == IF RandomElement(Colors) = "Red" THEN "Red" ELSE "Blue" IN
               /\ color' = [color EXCEPT ![n] = col]
               /\ UNCHANGED <<msgs, pc, sample, iter>>
        end either;
    end while;
end process;

process (Loop = SlushLoopProcess)
variables lp;
begin
LoopStep:
    while TRUE do
        either
            /\ pc[lp] = "waitColor"
            /\ color[LoopHost(lp)] # NoColor
            /\ pc' = [pc EXCEPT ![lp] = "sample"]
            /\ UNCHANGED <<color, msgs, sample, iter>>
        or
            /\ pc[lp] = "sample"
            /\ LET peers == RandomSubset(SlushQueryProcess \\ {lp}, SampleSetSize) IN
               /\ sample' = [sample EXCEPT ![lp] = peers]
               /\ msgs' = msgs \cup { [type |-> "query",
                                      from |-> lp,
                                      to   |-> qp,
                                      color|-> color[LoopHost(lp)]] :
                                      qp \in peers }
               /\ pc' = [pc EXCEPT ![lp] = "collect"]
               /\ UNCHANGED <<color, iter>>
        or
            /\ pc[lp] = "collect"
            /\ \A qp \in sample[lp] :
               \E m \in msgs :
                 /\ m.type = "reply"
                 /\ m.from = qp
                 /\ m.to   = lp
            /\ (* tally replies *)
               LET replies == { m \in msgs :
                                 /\ m.type = "reply"
                                 /\ m.to   = lp } IN
               LET cntRed == Cardinality({ r \in replies : r.color = "Red"}) IN
               LET cntBlue == Cardinality({ r \in replies : r.color = "Blue"}) IN
               /\ color' = IF cntRed >= PickFlipThreshold THEN
                              [color EXCEPT ![LoopHost(lp)] = "Red"]
                          ELSE IF cntBlue >= PickFlipThreshold THEN
                              [color EXCEPT ![LoopHost(lp)] = "Blue"]
                          ELSE color
               /\ msgs'   = msgs \ { m \in msgs :
                                      /\ m.type = "reply"
                                      /\ m.to   = lp }
               /\ sample' = [sample EXCEPT ![lp] = {}]
               /\ iter'   = [iter EXCEPT ![lp] = @ + 1]
               /\ IF iter'[lp] >= SlushIterationCount THEN
                     /\ pc' = [pc EXCEPT ![lp] = "done"]
                     /\ msgs' = msgs' \cup { [type |-> "term", from |-> lp,
                                               to   |-> "All", color |-> NoColor] }
                  ELSE
                     /\ pc' = [pc EXCEPT ![lp] = "sample"]
                     /\ UNCHANGED msgs'
        or
            /\ pc[lp] = "done"
            /\ UNCHANGED <<color, msgs, pc, sample, iter>>
        end either;
    end while;
end process;

process (Query = SlushQueryProcess)
variables qp;
begin
QueryStep:
    while TRUE do
        either
            /\ pc[qp] = "reply"
            /\ \E m \in msgs :
                 /\ m.type = "query"
                 /\ m.to   = qp
                 /\ LET srcColor == m.color IN
                    /\ IF color[QueryHost(qp)] = NoColor
                       THEN color' = [color EXCEPT ![QueryHost(qp)] = srcColor]
                       ELSE color' = color
                    /\ msgs' = msgs \ {m}
                               \cup { [type |-> "reply",
                                      from |-> qp,
                                      to   |-> m.from,
                                      color|-> color'[QueryHost(qp)]] }
                    /\ UNCHANGED <<pc, sample, iter>>
            /\ pc' = [pc EXCEPT ![qp] = "reply"]  \* remain in reply state
        or
            /\ AllLoopsDone
            /\ pc' = [pc EXCEPT ![qp] = "queryDone"]
            /\ UNCHANGED <<color, msgs, sample, iter>>
        or
            /\ pc[qp] = "queryDone"
            /\ UNCHANGED <<color, msgs, pc, sample, iter>>
        end either;
    end while;
end process;
end algorithm *)

\* Since PlusCal is not actually executed here, we provide the equivalent TLA+ actions.

ClientAssign ==
    /\ pc["Client"] = "client"
    /\ \E n \in UncoloredNodes :
         \E col \in Colors :
            /\ color' = [color EXCEPT ![n] = col]
            /\ pc'    = [pc EXCEPT !["Client"] = "client"]
            /\ UNCHANGED <<msgs, sample, iter>>
    /\ UNCHANGED <<pc, sample, iter>> \* other variables unchanged

LoopRequireColor ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "waitColor"
         /\ color[LoopHost(lp)] # NoColor
         /\ pc' = [pc EXCEPT ![lp] = "sample"]
         /\ UNCHANGED <<color, msgs, sample, iter>>

LoopSample ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "sample"
         /\ LET peers == Subset(SlushQueryProcess \\ {lp}, SampleSetSize) IN
            /\ sample' = [sample EXCEPT ![lp] = peers]
            /\ msgs'   = msgs \cup { [type  |-> "query",
                                      from  |-> lp,
                                      to    |-> qp,
                                      color |-> color[LoopHost(lp)]] :
                                      qp \in peers }
            /\ pc' = [pc EXCEPT ![lp] = "collect"]
            /\ UNCHANGED <<color, iter>>
    /\ UNCHANGED <<pc, sample, iter>> \* variables not mentioned stay

QueryRespond ==
    /\ \E m \in msgs :
         /\ m.type = "query"
         /\ LET qp  == m.to
                src == m.color
                n   == QueryHost(qp) IN
            /\ color' = IF color[n] = NoColor
                        THEN [color EXCEPT ![n] = src]
                        ELSE color
            /\ msgs' = (msgs \ {m}) \cup
                       { [type  |-> "reply",
                          from  |-> qp,
                          to    |-> m.from,
                          color |-> color'[n]] }
            /\ UNCHANGED <<pc, sample, iter>>
    /\ UNCHANGED <<color, msgs>> \* for other cases

LoopCollect ==
    /\ \E lp \in SlushLoopProcess :
         /\ pc[lp] = "collect"
         /\ \A qp \in sample[lp] :
                \E r \in msgs :
                    /\ r.type = "reply"
                    /\ r.from = qp
                    /\ r.to   = lp
         /\ LET replies == { r \in msgs :
                               /\ r.type = "reply"
                               /\ r.to   = lp } IN
            LET cntRed  == Cardinality({ r \in replies : r.color = "Red"}) IN
            LET cntBlue == Cardinality({ r \in replies : r.color = "Blue"}) IN
            /\ color' = IF cntRed >= PickFlipThreshold THEN
                            [color EXCEPT ![LoopHost(lp)] = "Red"]
                        ELSE IF cntBlue >= PickFlipThreshold THEN
                            [color EXCEPT ![LoopHost(lp)] = "Blue"]
                        ELSE color
            /\ msgsTmp = msgs \ { r \in msgs :
                                    /\ r.type = "reply"
                                    /\ r.to   = lp }
            /\ iter' = [iter EXCEPT ![lp] = @ + 1]
            /\ IF iter'[lp] >= SlushIterationCount THEN
                  /\ pc'    = [pc EXCEPT ![lp] = "done"]
                  /\ msgs'  = msgsTmp \cup
                               { [type |-> "term", from |-> lp,
                                  to   |-> "All", color |-> NoColor] }
               ELSE
                  /\ pc'    = [pc EXCEPT ![lp] = "sample"]
                  /\ msgs'  = msgsTmp
            /\ sample' = [sample EXCEPT ![lp] = {}]
    /\ UNCHANGED <<color, pc, sample, iter>> \* variables not changed in other branches

TerminateAll ==
    /\ AllLoopsDone
    /\ pc' = [pc EXCEPT ![p \in SlushQueryProcess] = "queryDone"]
    /\ UNCHANGED <<color, msgs, sample, iter>>

Next ==
    \/ ClientAssign
    \/ LoopRequireColor
    \/ LoopSample
    \/ QueryRespond
    \/ LoopCollect
    \/ TerminateAll

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<color, msgs, pc, sample, iter>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
MessageSet == { m \in Message :
                /\ m.type \in {"query","reply","term"}
                /\ m.from \in Process
                /\ m.to   \in Process
                /\ m.color \in Colors \cup {NoColor} }

PCMap == [p \in Process |-> PCValues]

TypeInvariant ==
    /\ color \in [Node -> (Colors \cup {NoColor})]
    /\ msgs  \subseteq MessageSet
    /\ pc    \in [Process -> PCValues]
    /\ sample \in [SlushLoopProcess -> SUBSET SlushQueryProcess]
    /\ iter   \in [SlushLoopProcess -> Nat]

====