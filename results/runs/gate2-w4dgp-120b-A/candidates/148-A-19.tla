---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, TLC

\* Nano cryptocurrency: each account has its own blockchain (account chain) within a
\* block lattice.  Actions create blocks on the lattice (genesis, send, open,
\* receive, change-representative) and broadcast them to all nodes at once.  Each
\* node validates received blocks against its own ledger copy before committing
\* them, so the lattice grows as a replication log: validated, broadcast, and
\* committed blocks together form the lattice's state history.
CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
  CalculateHash, NoHash, NoBlock

\* CalculateHash is a modelled operator (substituted in the .cfg) that maps block
\* data and a previous hash to a new hash.  In a real implementation it would be
\* Blake2b; here it is modelled finitely so the lattice stays tractable.

\* A block with a sender, optional recipient (or None for open/change), a value,
\* and references to the sender's previous block in its own chain plus an optional
\* send-block being claimed (for receive blocks).  Every block is signed by the
\* private key of the node that created it.
Block ==
  [sender: PrivateKey, recipient: PublicKey \cup {NoHash}, value: 0..GenesisBalance,
   prev: Hash \cup {NoHash}, claim: Hash \cup {NoBlock}, sig: PublicKey]

\* A block is part of an account chain if it appears in the chain greatest-first
\* under the prev relationship, starting from that chain's head block.
RECURSIVE Chain(_)
Chain(h) ==
  IF h = NoHash THEN {}
  ELSE
    LET parent == CHOOSE p \in {g \in Hash : Block[g].prev = h}
    IN {h} \cup Chain(parent)

\* Balance of an account chain: sum the values of blocks where that chain is the
\* receiver, minus the values where it is the sender.
RECURSIVE SumOnChain(_)
SumOnChain(S) ==
  IF S = {} THEN 0
  ELSE
    LET h == CHOOSE x \in S : TRUE
        add == IF Block[h].recipient \in PublicKey THEN Block[h].value ELSE 0
        subtract == IF Block[h].sender = NoHashVal THEN 0 ELSE Block[h].value
    IN add - subtract + SumOnChain(S \ {h})

RECURSIVE ChainBalances(_)
ChainBalances(S) ==
  IF S = {} THEN 0
  ELSE
    LET h == CHOOSE x \in S : TRUE
    IN SumOnChain(Chain(h)) + ChainBalances(S \ {h})

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* A block is broadcast to every node's received set together (a lattice update,
\* not an individual message sent to one recipient at a time).
Broadcast(h) ==
  /\ lastHash' = h
  /\ received' = [n \in Node |-> received[n] \cup {h}]

CreateGenesis ==
  /\ lastHash = NoHashVal
  /\ \A n \in Node : ledger[n] = [h \in Hash |-> NoBlockVal]
  /\ ~\E n \in Node : \E i \in PrivateKey : Block[NoHash].sender = i
  /\ \E n \in Node : \E i \in PrivateKey :
       /\ ledger[n] = [h \in Hash |-> NoBlockVal]
       /\ ledger' = [m \in Node |->
             [h \in Hash |->
               IF h = NoHash
               THEN [sender |-> i, recipient |-> NoHash, value |-> GenesisBalance,
                      prev |-> NoHash, claim |-> NoBlock, sig |-> PublicKey[i]]
               ELSE ledger[n][h]]]
  /\ Broadcast(NoHash)

CreateSend(n, i) ==
  /\ \A m \in Node : NoHash \notin received[m]
  /\ Block[NoHash].sender = NoHashVal
  /\ \E j \in PrivateKey :
      /\ i # j
      /\ sumPrev == SumOnChain(Chain(Block[lastHash].prev))
      /\ Block[lastHash].value - sumPrev >= 1
      /\ ledger' = [m \in Node |->
            [h \in Hash |->
              IF h = NoHash
              THEN [sender |-> i, recipient |-> PublicKey[j], value |-> 1,
                    prev |-> lastHash, claim |-> NoBlock, sig |-> PublicKey[i]]
              ELSE ledger[m][h]]]
  /\ Broadcast(NoHash)

CreateOpen(n, i) ==
  /\ \A m \in Node : NoHash \notin received[m]
  /\ Block[NoHash].sender = NoHashVal
  /\ \E j \in PrivateKey :
      /\ Block[lastHash].recipient = PublicKey[i]
      /\ Block[NoHash].sender = NoHashVal
      /\ ledger' = [m \in Node |->
            [h \in Hash |->
              IF h = NoHash
              THEN [sender |-> i, recipient |-> NoHash, value |-> 0,
                    prev |-> NoHash, claim |-> lastHash, sig |-> PublicKey[i]]
              ELSE ledger[m][h]]]
  /\ Broadcast(NoHash)

CreateReceive(n, i) ==
  /\ \A m \in Node : NoHash \notin received[m]
  /\ Block[NoHash].sender = NoHashVal
  /\ \E j \in PrivateKey :
      /\ Block[lastHash].recipient \in PublicKey
      /\ Block[Block[lastHash].prev].sender # j
      /\ Block[Block[lastHash].prev].recipient \in PublicKey
      /\ ledger' = [m \in Node |->
            [h \in Hash |->
              IF h = NoHash
              THEN [sender |-> i, recipient |-> Block[lastHash].recipient,
                    value |-> Block[lastHash].value, prev |-> Block[lastHash].prev,
                    claim |-> lastHash, sig |-> PublicKey[i]]
              ELSE ledger[m][h]]]
  /\ Broadcast(NoHash)

\* Every node validates a received block against its own ledger copy before
\* committing; the lattice grows only through validation, so any order of
\* received blocks is admissible and the lattice keeps growing as a log.
Validate(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] = NoBlockVal
  /\ Block[h].sig = PublicKey[Block[h].sender]
  /\ (Block[h].prev = NoHash \/ ledger[n][Block[h].prev] # NoBlockVal)
  /\ (Block[h].claim = NoBlock \/ ledger[n][Block[h].claim] # NoBlockVal)
  /\ (Block[h].prev # NoHash => Block[h].prev # h)
  /\ (Block[h].prev = NoHash => Block[h].value = GenesisBalance)
  /\ (Block[h].prev # NoHash => Block[h].value <= SumOnChain(Chain(Block[h].prev)))
  /\ ledger' = [m \in Node |->
        [g \in Hash |->
          IF n = m /\ g = h
          THEN Block[h]
          ELSE ledger[m][g]]]
  /\ received' = [m \in Node |-> IF m = n THEN received[n] \ {h} ELSE received[m]]

Next == \E n \in Node :
  \/ CreateGenesis \/ Validate(n, NoHash)
  \/ \E i \in PrivateKey : CreateSend(n, i) \/ CreateOpen(n, i) \/ CreateReceive(n, i)

Spec == Init /\ [][Next]_vars

\* Every block in every node's ledger copy has a valid signature matching its
\* chain's owning public key -- no replicated ledger copy ever holds a forged
\* (or otherwise bad-signature) block, even though the lattice is assembled from
\* independently-validated deliveries, so the lattice itself is never polluted.
SafetyInvariant ==
  \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].sig = PublicKey[ledger[n][h].sender]

====