---- MODULE Slush ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* Set of loop process identifiers
    SlushQueryProcess,  \* Set of query process identifiers
    HostMapping,        \* Function mapping each process (loop or query) to its host node
    SlushIterationCount,\* Number of iterations each loop process performs
    SampleSetSize,      \* Size of the peer sample taken each iteration
    PickFlipThreshold,  \* Threshold for flipping to a color
    NoColor,            \* Value representing an uncolored node
    NoMessage           \* Placeholder value for messages that carry no color

\* ----------------------------------------------------------------------
\* Colors used by the protocol
\* ----------------------------------------------------------------------
ColorSet == {"Red", "Blue"}

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Message ==
    [ type  : {"query", "reply", "term"},
      src   : (SlushLoopProcess \cup SlushQueryProcess),
      dst   : (SlushLoopProcess \cup SlushQueryProcess),
      color : (ColorSet \cup {NoColor, NoMessage}) ]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    colors,          \* [Node -> (ColorSet \cup {NoColor})]
    msgs,            \* Set of in‑flight messages
    sampleSet,       \* [SlushLoopProcess -> SUBSET Node]
    iterCount        \* [SlushLoopProcess -> Nat]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Host(p) == HostMapping[p]

QueryProc(node) ==
    CHOOSE qp \in SlushQueryProcess : Host(qp) = node

\* ----------------------------------------------------------------------
\* PlusCal algorithm
\* ----------------------------------------------------------------------
(*--algorithm SlushAlg
variables colors, msgs, sampleSet, iterCount;

begin
  client:
    while \E n \in Node : colors[n] = NoColor do
      choose n \in Node : colors[n] = NoColor;
      choose c \in ColorSet;
      colors := [colors EXCEPT ![n] = c];
    end while;

  loop(p \in SlushLoopProcess):
    let node == Host(p) in
      await colors[node] # NoColor;
      while iterCount[p] < SlushIterationCount do
        \* --- sample peers ---
        with peers == { n \in Node : n # node } do
          choose sample \in SUBSET peers : Cardinality(sample) = SampleSetSize;
          sampleSet := [sampleSet EXCEPT ![p] = sample];
          \* send query messages to the query processes of the sampled nodes
          with qps == { qp \in SlushQueryProcess : Host(qp) \in sample } do
            msgs := msgs \cup
              { [type |-> "query",
                 src  |-> p,
                 dst  |-> qp,
                 color|-> colors[node] ] : qp \in qps };
          end with;
        end with;

        \* --- wait for all replies ---
        await \A qp \in SlushQueryProcess :
                (Host(qp) \in sampleSet[p]) =>
                (\E m \in msgs :
                    m.type = "reply" /\ m.dst = p /\ m.src = qp);

        \* --- tally replies and possibly flip color ---
        with reds == Cardinality(
                     { m \in msgs :
                         m.type = "reply" /\ m.dst = p /\ m.color = "Red" }) do
          with blues == Cardinality(
                      { m \in msgs :
                          m.type = "reply" /\ m.dst = p /\ m.color = "Blue" }) do
            if reds >= PickFlipThreshold then
                colors := [colors EXCEPT ![node] = "Red"];
            elsif blues >= PickFlipThreshold then
                colors := [colors EXCEPT ![node] = "Blue"];
            else
                skip;
            end if;
            \* remove processed replies
            msgs := msgs \ { m \in msgs :
                               m.type = "reply" /\ m.dst = p };
            \* reset sample set and increment iteration counter
            sampleSet := [sampleSet EXCEPT ![p] = {}];
            iterCount := [iterCount EXCEPT ![p] = @ + 1];
          end with;
        end with;
      end while;

      \* --- broadcast termination ---
      msgs := msgs \cup
               { [type |-> "term",
                  src  |-> p,
                  dst  |-> qp,
                  color|-> NoMessage] : qp \in SlushQueryProcess };
      skip;
    end let;

  query(q \in SlushQueryProcess):
    let node == Host(q) in
      while TRUE do
        either
          \* --- handle a query message ---
          /\ \E m \in msgs :
                m.type = "query" /\ m.dst = q
          /\ let m == CHOOSE mm \in msgs :
                     mm.type = "query" /\ mm.dst = q in
               \* adopt the queried color if uncolored
               if colors[node] = NoColor then
                 colors := [colors EXCEPT ![node] = m.color];
               else
                 skip;
               end if;
               \* reply with current color
               msgs := (msgs \ {m}) \cup
                        { [type |-> "reply",
                           src  |-> q,
                           dst  |-> m.src,
                           color|-> colors[node]] };
          end let
        or
          \* --- handle a termination message ---
          /\ \E m \in msgs :
                m.type = "term" /\ m.dst = q
          /\ let m == CHOOSE mm \in msgs :
                     mm.type = "term" /\ mm.dst = q in
               msgs := msgs \ {m};
               goto Done;
          end let
        end either;
      end while;
    Done: skip;
end algorithm; *)

\* ----------------------------------------------------------------------
\* The behavior of the algorithm
\* ----------------------------------------------------------------------
vars == << colors, msgs, sampleSet, iterCount >>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ colors \in [Node -> (ColorSet \cup {NoColor})]
    /\ msgs \subseteq Message

====