---- MODULE Slush ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Node,               \* Set of node identifiers
    SlushLoopProcess,   \* Set of loop process identifiers (one per node)
    SlushQueryProcess,  \* Set of query process identifiers (one per node)
    HostMapping,        \* Set of triples <<n, lp, qp>> linking a node with its loop and query processes
    SlushIterationCount,\* Number of iterations each loop process must perform
    SampleSetSize,      \* Size of the random peer sample taken each iteration
    PickFlipThreshold,  \* Minimum number of identical replies needed to flip a node's color
    NoColor,            \* Special value denoting an uncolored node
    NoMessage           \* Special value denoting the absence of a message

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Color == {"Red", "Blue"}

\* Mapping from a loop process to its host node
NodeOfLoop(lp) == 
    CHOOSE n \in Node : <<n, lp, q>> \in HostMapping

\* Mapping from a loop process to its query process
QueryOfLoop(lp) ==
    CHOOSE q \in SlushQueryProcess : <<NodeOfLoop(lp), lp, q>> \in HostMapping

\* Mapping from a query process to its host node
NodeOfQuery(qp) ==
    CHOOSE n \in Node : <<n, lp, qp>> \in HostMapping

\* Mapping from a query process to its loop process
LoopOfQuery(qp) ==
    CHOOSE lp \in SlushLoopProcess : <<NodeOfQuery(qp), lp, qp>> \in HostMapping

\* All query processes except the one that belongs to the given loop process
OtherQueryProcs(lp) == { qp \in SlushQueryProcess : qp # QueryOfLoop(lp) }

\* A nondeterministic sample of size SampleSetSize drawn from the other query processes
Sample(lp) == 
    CHOOSE s \subseteq OtherQueryProcs(lp) : Cardinality(s) = SampleSetSize

\* Message record definitions
QueryMsg == [type : {"query"}, src : SlushLoopProcess, dst : SlushQueryProcess, color : Color]
ReplyMsg == [type : {"reply"}, src : SlushQueryProcess, dst : SlushLoopProcess, color : Color]
TermMsg  == [type : {"term"},  src : SlushLoopProcess, dst : SlushQueryProcess]

Message == UNION { {msg \in QueryMsg}, {msg \in ReplyMsg}, {msg \in TermMsg} }

\* ----------------------------------------------------------------------
\* PlusCal algorithm
\* ----------------------------------------------------------------------
(*--algorithm SlushAlg
variables
    colors \in [Node -> (Color \cup {NoColor})],
    msgs   \in SUBSET Message,
    iter   \in [SlushLoopProcess -> Nat],
    sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess];

begin
\* ---------------------------------------------------------------
\* Client process – assigns initial colors to uncolored nodes
\* ---------------------------------------------------------------
process (client = "client")
variables
    n;
  while TRUE do
    with n \in Node :
      if colors[n] = NoColor then
        either
          colors' = [colors EXCEPT ![n] = "Red"]
        or
          colors' = [colors EXCEPT ![n] = "Blue"]
        end either;
        skip
      else
        skip
      end if;
    end with;
    if \A n \in Node : colors[n] # NoColor then
      halt;
    end if;
  end while;
end process;

\* ---------------------------------------------------------------
\* Loop processes – drive the Slush iteration
\* ---------------------------------------------------------------
process (lp \in SlushLoopProcess)
variables
    n   \in Node,
    s   \in SUBSET SlushQueryProcess,
    replies \in [SlushQueryProcess -> Color];
  n := NodeOfLoop(lp);
  while TRUE do
    \* Wait until the host node is colored
    await colors[n] # NoColor;

    \* Check if the required number of iterations has been performed
    if iter[lp] < SlushIterationCount then
      \* Choose a random sample of peers
      s := Sample(lp);
      sampleSet' = [sampleSet EXCEPT ![lp] = s];

      \* Send query messages to the sampled query processes
      with q \in s do
        msgs' = msgs \cup {
          [type |-> "query",
           src  |-> lp,
           dst  |-> q,
           color|-> colors[n]]
        };
      end with;

      \* Wait for replies from all sampled peers
      await \A q \in s :
        \E m \in msgs : /\ m.type = "reply"
                         /\ m.src = q
                         /\ m.dst = lp;

      \* Tally the replies
      with r \in Color :
        let cnt == Cardinality({ q \in s :
                                   \E m \in msgs :
                                      /\ m.type = "reply"
                                      /\ m.src = q
                                      /\ m.dst = lp
                                      /\ m.color = r }) in
          if cnt >= PickFlipThreshold then
            colors' = [colors EXCEPT ![n] = r];
          else
            skip;
          end if;
      end with;

      \* Remove processed reply messages
      msgs' = msgs \ { m \in msgs :
                        /\ m.type = "reply"
                        /\ m.dst = lp };

      \* Increment iteration counter and clear sample
      iter' = [iter EXCEPT ![lp] = @ + 1];
      sampleSet' = [sampleSet EXCEPT ![lp] = {}];
    else
      \* Broadcast termination messages
      with q \in SlushQueryProcess do
        msgs' = msgs \cup {
          [type |-> "term",
           src  |-> lp,
           dst  |-> q]
        };
      end with;
      halt;
    end if;
  end while;
end process;

\* ---------------------------------------------------------------
\* Query processes – answer queries and possibly adopt a color
\* ---------------------------------------------------------------
process (qp \in SlushQueryProcess)
variables
    n \in Node;
  n := NodeOfQuery(qp);
  while TRUE do
    either
      \* Respond to a query
      await \E m \in msgs :
              /\ m.type = "query"
              /\ m.dst = qp;
      with m \in msgs :
        /\ m.type = "query"
        /\ m.dst = qp do
          \* If uncolored, adopt the queried color
          if colors[n] = NoColor then
            colors' = [colors EXCEPT ![n] = m.color];
          else
            skip;
          end if;
          \* Send a reply back
          msgs' = msgs \cup {
            [type |-> "reply",
             src  |-> qp,
             dst  |-> m.src,
             color|-> colors[n]]
          };
          \* Remove the processed query message
          msgs' = msgs' \ {m};
        end with;
    or
      \* Receive a termination message and exit
      await \E m \in msgs :
              /\ m.type = "term"
              /\ m.dst = qp;
      with m \in msgs :
        /\ m.type = "term"
        /\ m.dst = qp do
          msgs' = msgs \ {m};
          halt;
        end with;
    end either;
  end while;
end process;

end algorithm *)

\* ----------------------------------------------------------------------
\* Translation of the PlusCal algorithm
\* ----------------------------------------------------------------------
VARIABLES colors, msgs, iter, sampleSet

\* The set of all variables that can change
Vars == <<colors, msgs, iter, sampleSet>>

\* Initial state (generated by PlusCal)
Init == 
    /\ colors = [n \in Node |-> NoColor]
    /\ msgs = {}
    /\ iter = [lp \in SlushLoopProcess |-> 0]
    /\ sampleSet = [lp \in SlushLoopProcess |-> {}]

\* Next-state relation (generated by PlusCal)
Next == 
    \/ \E self \in {"client"} : 
         \/ \E n \in Node :
              /\ colors[n] = NoColor
              /\ \/ colors' = [colors EXCEPT ![n] = "Red"]
                 \/ colors' = [colors EXCEPT ![n] = "Blue"]
              /\ UNCHANGED <<msgs, iter, sampleSet>>
         \/ (\A n \in Node : colors[n] # NoColor) /\ UNCHANGED <<colors, msgs, iter, sampleSet>>
    \/ \E lp \in SlushLoopProcess :
         LET n == NodeOfLoop(lp) IN
         IF iter[lp] < SlushIterationCount THEN
           \* Choose a sample
           \E s \in SUBSET OtherQueryProcs(lp) :
               /\ Cardinality(s) = SampleSetSize
               /\ sampleSet' = [sampleSet EXCEPT ![lp] = s]
               /\ \A q \in s :
                      msgs' = msgs \cup {
                        [type |-> "query",
                         src  |-> lp,
                         dst  |-> q,
                         color|-> colors[n]]
                      }
               /\ \A q \in s :
                      \E m \in msgs' :
                        /\ m.type = "reply"
                        /\ m.src = q
                        /\ m.dst = lp
               /\ \E r \in Color :
                      LET cnt == Cardinality({ q \in s :
                                  \E m \in msgs' :
                                      /\ m.type = "reply"
                                      /\ m.src = q
                                      /\ m.dst = lp
                                      /\ m.color = r }) IN
                      IF cnt >= PickFlipThreshold THEN
                        colors' = [colors EXCEPT ![n] = r]
                      ELSE
                        UNCHANGED colors
               /\ msgs' = msgs' \ { m \in msgs' :
                                      /\ m.type = "reply"
                                      /\ m.dst = lp }
               /\ iter' = [iter EXCEPT ![lp] = @ + 1]
               /\ UNCHANGED sampleSet
         ELSE
           \* Broadcast termination
           \E q \in SlushQueryProcess :
               msgs' = msgs \cup {
                 [type |-> "term",
                  src  |-> lp,
                  dst  |-> q]
               }
           /\ UNCHANGED <<colors, iter, sampleSet>>
         END
    \/ \E qp \in SlushQueryProcess :
         LET n == NodeOfQuery(qp) IN
         \/ \E m \in msgs :
               /\ m.type = "query"
               /\ m.dst = qp
               /\ 
               (   IF colors[n] = NoColor THEN
                       colors' = [colors EXCEPT ![n] = m.color]
                   ELSE
                       UNCHANGED colors
               )
               /\ msgs' = msgs \cup {
                     [type |-> "reply",
                      src  |-> qp,
                      dst  |-> m.src,
                      color|-> colors[n]]
                  }
               /\ msgs' = msgs' \ {m}
               /\ UNCHANGED <<iter, sampleSet>>
         \/ \E m \in msgs :
               /\ m.type = "term"
               /\ m.dst = qp
               /\ msgs' = msgs \ {m}
               /\ UNCHANGED <<colors, iter, sampleSet>>
         )
    \/ UNCHANGED Vars

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ colors \in [Node -> (Color \cup {NoColor})]
    /\ msgs \subseteq Message
    /\ iter \in [SlushLoopProcess -> Nat]
    /\ sampleSet \in [SlushLoopProcess -> SUBSET SlushQueryProcess]

====