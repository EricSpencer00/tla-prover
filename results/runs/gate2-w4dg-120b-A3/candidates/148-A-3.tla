---- MODULE Nano ----
EXTENDS Integers, Sequences

CONSTANTS
    Hash, NoHashVal,
    PrivateKey, PublicKey,
    Node, GenesisBalance,
    NoBlockVal, CalculateHash, NoHash

\* A block carries the hash of the previous block on the account chain,
\* so ordering is recorded in the data structure itself -- the source of
\* the super-exponential state space that makes full model checking hard.
Block == [prev : Hash \cup {NoHash}, sender : PublicKey, recv : PublicKey, amount : Nat, sig : PrivateKey]
EmptyDistLedger == [h \in Hash |-> NoBlockVal]

VARIABLES lastHash, distLedger, received
vars == <<lastHash, distLedger, received>>

PubOf == [k \in PrivateKey |-> CHOOSE pk \in PublicKey : k \in {q \in PrivateKey : pk = PubOf[q]}]

\* The distributed ledger is replicated across every node; each node also
\* keeps a set of received blocks still awaiting validation.
ReplicaDistLedger == distLedger[Node[1]]
ReplicaReceived == received[Node[1]]

\* The chain of blocks belonging to an account, from first to last.
ChainBlocks(acc) == [i \in Nat |-> CHOOSE h \in Hash : distLedger[i][h] # NoBlockVal /\ distLedger[i][h].sender = acc]

Balance(acc) ==
    LET Seq == CHOOSE s \in Seq(Real) :
                  \E f \in [Nat -> Hash]: ChainBlocks(acc) = [i \in Nat |-> f[i]] /\ s = ChainFrom(f)
    IN Seq[Len(Seq)]

ChainFrom(f) ==
    IF f[1] = NoHash THEN <<>>
    ELSE LET tail == ChainFrom(f[f[1]])
         IN <<[hash |-> f[1], sender |-> distLedger[f[1]][f[1]].sender, recv |-> distLedger[f[1]][f[1]].recv, amount |-> distLedger[f[1]][f[1]].amount]>>

RECURSIVE SumChain(_)
SumChain(s) == IF s = <<>> THEN 0 ELSE Head(s).amount + SumChain(Tail(s))

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distLedger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
    /\ received \in [Node -> SUBSET [hash : Hash, recv : Node]]

Init ==
    /\ lastHash = NoHash
    /\ distLedger = [i \in Node |-> EmptyDistLedger]
    /\ received = [i \in Node |-> {}]

\* The safety-critical check: a block's signature must match the public
\* key of the account that owns the chain the block belongs to.
ValidSignature(b) == PubOf[b.sig] = distLedger[b.recv][b.prev].sender

CreateGenBlock(node, key) ==
    /\ lastHash = NoHash
    /\ distLedger[Node[1]] = EmptyDistLedger
    /\ LET tx == [prev |-> NoHash, sender |-> PubOf[key], recv |-> PubOf[key], amount |-> GenesisBalance, sig |-> key]
           h == CalculateHash(tx, NoHashVal)
       IN /\ lastHash' = h
          /\ distLedger' = [i \in Node |-> [distLedger[i] EXCEPT ![h] = tx]]
          /\ received' = [i \in Node |-> {}]

CreateSendBlock(node, key, target) ==
    /\ lastHash # NoHash
    /\ LET tx == [prev |-> lastHash, sender |-> PubOf[key], recv |-> target, amount |-> 1, sig |-> key]
           h == CalculateHash(tx, NoHashVal)
       IN /\ Balance(PubOf[key]) >= 1
          /\ distLedger' = [i \in Node |-> [distLedger[i] EXCEPT ![h] = tx]]
          /\ lastHash' = h
          /\ received' = [i \in Node |-> received[i] \cup {[hash |-> h, recv |-> node]}]

CreateOpenBlock(node, key, send) ==
    /\ lastHash # NoHash
    /\ \A r \in received: r.hash # send
    /\ LET tx == [prev |-> NoHash, sender |-> distLedger[send][send].sender, recv |-> PubOf[key], amount |-> 0, sig |-> key]
           h == CalculateHash(tx, NoHashVal)
       IN /\ distLedger' = [i \in Node |-> [distLedger[i] EXCEPT ![h] = tx]]
          /\ lastHash' = h
          /\ received' = [i \in Node |-> received[i] \cup {[hash |-> h, recv |-> node]}]

CreateReceiveBlock(node, key, send) ==
    /\ lastHash # NoHash
    /\ \A r \in received: r.hash # send
    /\ LET tx == [prev |-> ReplicaDistLedger[node].prev,
                  sender |-> ReplicaDistLedger[node].sender,
                  recv |-> PubOf[key],
                  amount |-> ReplicaDistLedger[node].amount + 1,
                  sig |-> key]
           h == CalculateHash(tx, NoHashVal)
       IN /\ distLedger' = [i \in Node |-> [distLedger[i] EXCEPT ![h] = tx]]
          /\ lastHash' = h
          /\ received' = [i \in Node |-> received[i] \cup {[hash |-> h, recv |-> node]}]

CreateChangeRepresentative(node, key) ==
    /\ lastHash # NoHash
    /\ LET tx == [prev |-> ReplicaDistLedger[node].prev,
                  sender |-> ReplicaDistLedger[node].sender,
                  recv |-> PubOf[key],
                  amount |-> ReplicaDistLedger[node].amount,
                  sig |-> key]
           h == CalculateHash(tx, NoHashVal)
       IN /\ distLedger' = [i \in Node |-> [distLedger[i] EXCEPT ![h] = tx]]
          /\ lastHash' = h
          /\ received' = [i \in Node |-> received[i] \cup {[hash |-> h, recv |-> node]}]

ValidateBlock(node, r) ==
    /\ r \in received[node]
    /\ distLedger' = [i \in Node |-> [distLedger[i] EXCEPT ![r.hash] = ReplicaDistLedger[node]]
    /\ received' = [i \in Node |-> received[i] \ {r}]
    /\ UNCHANGED lastHash

Next ==
    \/ \E key \in PrivateKey : CreateGenBlock(Node[1], key)
    \/ \E node \in Node, key \in PrivateKey : CreateSendBlock(node, key, PubOf[key])
    \/ \E node \in Node, key \in PrivateKey, send \in Hash : CreateOpenBlock(node, key, send)
    \/ \E node \in Node, key \in PrivateKey, send \in Hash : CreateReceiveBlock(node, key, send)
    \/ \E node \in Node, key \in PrivateKey : CreateChangeRepresentative(node, key)
    \/ \E node \in Node, r \in received[node] : ValidateBlock(node, r)

Spec == Init /\ [][Next]_vars

\* The only integrity requirement not covered by type invariants: every
\* block in every replica node's ledger carries a signature that matches
\* the public key of the account whose chain contains the block.
SafetyInvariant == \A i \in Node : \A h \in Hash : distLedger[i][h] # NoBlockVal => ValidSignature(distLedger[i][h])

====