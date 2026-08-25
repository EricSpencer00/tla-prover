---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Node,                \* set of node identifiers
    SlushLoopProcess,    \* set of loop process identifiers (one per node)
    SlushQueryProcess,   \* set of query process identifiers (one per node)
    HostMapping,         \* set of triples <<node, loopProc, queryProc>>
    SlushIterationCount, \* number of iterations each loop process must perform
    SampleSetSize,       \* size of the peer sample taken each iteration
    PickFlipThreshold,   \* number of identical replies needed to flip a color
    NoColor,             \* special value meaning “uncolored”
    NoMessage            \* special value for “no message”

\* ----------------------------------------------------------------------
\* Colors used by the protocol
\* ----------------------------------------------------------------------
Color == {"Red", "Blue"}

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Message ==
    [type : {"query", "reply", "term"},
     src  : (SlushLoopProcess \cup SlushQueryProcess),
     dst  : (SlushLoopProcess \cup SlushQueryProcess \cup {"all"}),
     col  : (Color \cup {NoColor})]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    color,   \* node -> Color \cup {NoColor}
    msgs,    \* set of messages currently in flight
    sample,  \* loopProcess -> SUBSET SlushQueryProcess  (the current sample)
    iter     \* loopProcess -> Nat  (iterations already completed)

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
LoopNode(lp) == 
    CHOOSE n \in Node : \E q \in SlushQueryProcess : <<n, lp, q>> \in HostMapping

QueryNode(qp) ==
    CHOOSE n \in Node : \E l \in SlushLoopProcess : <<n, l, qp>> \in HostMapping

\* ----------------------------------------------------------------------
\* PlusCal algorithm
\* ----------------------------------------------------------------------
(*--algorithm SlushAlg
variables
  color = [n \in Node |-> NoColor];
  msgs   = {};
  sample = [p \in SlushLoopProcess |-> {}];
  iter   = [p \in SlushLoopProcess |-> 0];

process (client = "client")
begin
  ClientLoop:
    while \E n \in Node : color[n] = NoColor do
      with n \in { m \in Node : color[m] = NoColor } do
        either
          color' = [color EXCEPT ![n] = "Red"]
        [] 
          color' = [color EXCEPT ![n] = "Blue"]
        end either;
      end with;
    end while;
end process;

process (lp \in SlushLoopProcess)
begin
  Init:
    await (\E n \in Node : <<n, lp, _>> \in HostMapping /\ color[n] # NoColor);
    skip; \* (host node already colored)

  Loop:
    if iter[lp] < SlushIterationCount then
      \* ---- sample a set of peers ----
      with peerSet \in SUBSET SlushQueryProcess :
        /\ Cardinality(peerSet) = SampleSetSize
        /\ \A q \in peerSet : q # lp
        /\ sample' = [sample EXCEPT ![lp] = peerSet];
        /\ \A q \in peerSet :
            let n == LoopNode(lp) in
            msgs' = msgs \cup { [type |-> "query",
                                 src  |-> lp,
                                 dst  |-> q,
                                 col  |-> color[n]] };
      end with;

      \* ---- wait for all replies ----
      await (\A q \in sample[lp] :
                \E m \in msgs : m.type = "reply" /\ m.dst = lp /\ m.src = q);

      \* ---- tally replies ----
      let reds   == { q \in sample[lp] :
                       \E m \in msgs :
                         m.type = "reply" /\ m.dst = lp /\ m.src = q /\ m.col = "Red" };
          blues  == sample[lp] \ reds;
          redCnt == Cardinality(reds);
          bluCnt == Cardinality(blues) in
        if redCnt >= PickFlipThreshold then
          color' = [color EXCEPT ![LoopNode(lp)] = "Red"]
        elsif bluCnt >= PickFlipThreshold then
          color' = [color EXCEPT ![LoopNode(lp)] = "Blue"]
        else
          skip;
        end if;
      end let;

      \* ---- clean up and advance iteration ----
      msgs'   = { m \in msgs :
                  ~ (m.type = "reply" /\ m.dst = lp) };
      sample' = [sample EXCEPT ![lp] = {}];
      iter'   = [iter EXCEPT ![lp] = @ + 1];
    else
      \* ---- termination broadcast ----
      msgs' = msgs \cup { [type |-> "term",
                           src  |-> lp,
                           dst  |-> "all",
                           col  |-> NoColor] };
    end if;
end process;

process (qp \in SlushQueryProcess)
begin
  QueryLoop:
    await \E m \in msgs : m.type = "query" /\ m.dst = qp;
    with m \in msgs :
      /\ m.type = "query"
      /\ m.dst  = qp
      \* possibly adopt the queried color if uncolored
      let n == QueryNode(qp) in
        if color[n] = NoColor then
          color' = [color EXCEPT ![n] = m.col]
        else
          skip
        endif;
      \* send reply
      msgs' = msgs \cup { [type |-> "reply",
                           src  |-> qp,
                           dst  |-> m.src,
                           col  |-> color[n]] };
      \* remove the processed query
      msgs' = msgs' \ {m};
    end with;
end process;
end algorithm; *)

\* ----------------------------------------------------------------------
\* The actions generated by PlusCal are Init and Next.
\* ----------------------------------------------------------------------
Spec == Init /\ [] [Next]_<<color, msgs, sample, iter>>

TypeInvariant ==
    /\ color \in [Node -> (Color \cup {NoColor})]
    /\ msgs \subseteq Message

====