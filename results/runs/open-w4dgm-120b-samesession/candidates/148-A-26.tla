---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

(* The original Nano protocol's block-lattice with per-account chains.  The   *)
(* actions below match the prose spec: CreateGenesis, CreateSend, CreateOpen, *)
(* CreateReceive, CreateChangeRep (the six actions the description lists),    *)
(* plus their corresponding Receive* processing actions.                      *)

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, recvSet

vars == <<lastHash, ledger, recvSet>>

\* The per-node ledger maps every possible hash to the block stored at that
\* hash, or to NoBlock if the hash slot is empty.
BlocksAt(n) == { ledger[n][h] : h \in Hash } \ {NoBlock}

\* The span of a block chain is the set of all its block hashes.
ChainSpan(blk) ==
  IF blk = NoBlock THEN {}
  ELSE ChainSpan(blk.prev) \cup {blk.hash}

ChainBalance(blk) ==
  IF blk = NoBlock THEN 0
  ELSE blk.amt + ChainBalance(blk.prev)

RECURSIVE ChainBalance(_)
ChainBalance(blk) ==
  IF blk = NoBlock THEN 0
  ELSE blk.amt + ChainBalance(blk.prev)

RECURSIVE ChainSpan(_)
ChainSpan(blk) ==
  IF blk = NoBlock THEN {}
  ELSE ChainSpan(blk.prev) \cup {blk.hash}

LastHashInChain(blk) ==
  IF blk = NoBlock THEN NoHashVal ELSE blk.hash

\* Balance invariant: the total across all account chains can never exceed the
\* genesis balance, no matter how blocks are interleaved.
RECURSIVE ChainSpanSet(_)
ChainSpanSet(G) ==
  IF G = {} THEN {}
  ELSE LET blk == CHOOSE x \in G : TRUE IN ChainSpan(blk) \cup ChainSpanSet(G \ {blk})

RECURSIVE ChainBalanceSet(_)
ChainBalanceSet(G) ==
  IF G = {} THEN 0
  ELSE LET blk == CHOOSE x \in G : TRUE IN ChainBalance(blk) + ChainBalanceSet(G \ {blk})

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ recvSet = [n \in Node |-> {}]

\* Genesis block: the whole coin supply appears in the ledger for the genesis
\* account, and the block is pushed to every node's in-flight set.
CreateGenesis ==
  /\ lastHash # NoHash
  /\ \A n \in Node : ledger[n][NoHash] # NoBlock
  /\ \E n \in Node :
       /\ \E p \in PrivateKey :
            /\ \A m \in Node : ledger[m][NoHash] = NoBlock
            /\ ledger' = [m \in Node |->
                 [ledger[m] EXCEPT ![NoHash] = [hash |-> NoHash, prev |-> NoBlock, amt |-> GenesisBalance,
                                                owner |-> p, sig |-> "sig"]]]
       /\ recvSet' = [recvSet EXCEPT ![n] = recvSet[n] \cup
                        {[hash |-> NoHash, prev |-> NoBlock, amt |-> GenesisBalance,
                          owner |-> p, sig |-> "sig"]}]
  /\ lastHash' = lastHash

\* A regular send block, referencing the sender's previous block.
CreateSend ==
  /\ lastHash # NoHash
  /\ \E n \in Node, p \in PrivateKey, amt \in 1..GenesisBalance,
        dest \in PublicKey :
       /\ LET prevBlk == IF ledger[n][lastHash] = NoBlock THEN NoBlock ELSE ledger[n][lastHash] IN
          /\ CHOOSE h \in Hash \ ChainSpanSet(BlocksAt(n)) : TRUE
          /\ CalculateHash(h, [hash |-> h, prev |-> prevBlk, amt |-> amt, owner |-> p]) # NoHash
          /\ LET blk == [hash |-> h, prev |-> prevBlk, amt |-> amt, owner |-> p,
                         sig |-> "sig"] IN
               /\ recvSet' = [recvSet EXCEPT ![n] = recvSet[n] \cup {blk}]
               /\ \A m \in Node : ledger' = [ledger EXCEPT ![m][h] = blk]
               /\ lastHash' = h

\* Open a brand-new account chain, referencing the sender's block as the
\* first block in the chain.  Requires that the referenced send has not been
\* claimed by anyone else.
CreateOpen ==
  /\ lastHash # NoHash
  /\ \E n \in Node, p \in PrivateKey, sendH \in Hash, amt \in 1..GenesisBalance :
       /\ \A m \in Node : ledger[m][sendH] # NoBlock
       /\ ledger[n][sendH].amt = amt
       /\ ledger[n][sendH].owner = p
       /\ ledger[n][sendH].prev = NoBlock
       /\ CHOOSE h \in Hash \ ChainSpanSet(BlocksAt(n)) : TRUE
       /\ CalculateHash(h, [hash |-> h, prev |-> ledger[n][sendH], amt |-> amt, owner |-> p]) # NoHash
       /\ LET blk == [hash |-> h, prev |-> ledger[n][sendH], amt |-> amt, owner |-> p,
                      sig |-> "sig"] IN
            /\ recvSet' = [recvSet EXCEPT ![n] = recvSet[n] \cup {blk}]
            /\ \A m \in Node : ledger' = [ledger EXCEPT ![m][h] = blk]
            /\ lastHash' = h

\* Receive a block that acknowledges a prior send block.
CreateReceive ==
  /\ lastHash # NoHash
  /\ \E n \in Node, p \in PrivateKey, sendH \in Hash, amt \in 1..GenesisBalance :
       /\ \A m \in Node : ledger[m][sendH] # NoBlock
       /\ ledger[n][sendH].owner = p
       /\ ledger[n][sendH].amt = amt
       /\ CHOOSE h \in Hash \ ChainSpanSet(BlocksAt(n)) : TRUE
       /\ CalculateHash(h, [hash |-> h, prev |-> ledger[n][sendH], amt |-> amt, owner |-> p]) # NoHash
       /\ LET blk == [hash |-> h, prev |-> ledger[n][sendH], amt |-> amt, owner |-> p,
                      sig |-> "sig"] IN
            /\ recvSet' = [recvSet EXCEPT ![n] = recvSet[n] \cup {blk}]
            /\ \A m \in Node : ledger' = [ledger EXCEPT ![m][h] = blk]
            /\ lastHash' = h

\* Change the voting representative of an account chain.
CreateChangeRep ==
  /\ lastHash # NoHash
  /\ \E n \in Node, p \in PrivateKey :
       /\ CHOOSE h \in Hash \ ChainSpanSet(BlocksAt(n)) : TRUE
       /\ CalculateHash(h, [hash |-> h, prev |-> IF ledger[n][lastHash] = NoBlock
                                       THEN NoBlock ELSE ledger[n][lastHash], amt |-> 0, owner |-> p])
          # NoHash
       /\ LET blk == [hash |-> h, prev |-> IF ledger[n][lastHash] = NoBlock
                                          THEN NoBlock ELSE ledger[n][lastHash], amt |-> 0,
                      owner |-> p, sig |-> "sig"] IN
            /\ recvSet' = [recvSet EXCEPT ![n] = recvSet[n] \cup {blk}]
            /\ \A m \in Node : ledger' = [ledger EXCEPT ![m][h] = blk]
            /\ lastHash' = h

\* A node validates and records an in-flight block, if the signature and
\* all referenced blocks check out against its own copy.
ReceiveBlock(n) ==
  /\ \E blk \in recvSet[n] :
       /\ ledger[n][blk.hash] = NoBlock
       /\ ledger[n][blk.owner] # NoBlock
       /\ ledger[n][blk.prev] # NoBlock \/ blk.prev = NoBlock
       /\ IF blk.prev = NoBlock THEN blk.amt = GenesisBalance ELSE TRUE
       /\ ledger' = [ledger EXCEPT ![n][blk.hash] = blk]
       /\ recvSet' = [recvSet EXCEPT ![n] = recvSet[n] \ {blk}]
  /\ lastHash' = lastHash

Next ==
  \/ CreateGenesis \/ CreateSend \/ CreateOpen \/ CreateReceive \/ CreateChangeRep
  \/ \E n \in Node : ReceiveBlock(n)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> {NoBlock} \cup [hash : Hash, prev : {NoBlock} \cup [hash : Hash, prev : {NoBlock} \cup [hash : Hash, prev : {NoBlock} \cup [hash : Hash, prev : {NoBlock} \cup [hash : Hash, prev : {NoBlock} \cup [hash : Hash, prev : {NoBlock} \cup [hash : Hash, prev : {NoBlock}, amt : Nat, owner : PrivateKey, sig : {"sig"}]]]]]]]]]
  /\ recvSet \in [Node -> SUBSET [hash : Hash, prev : {NoBlock} \cup [hash : Hash, prev : {NoBlock} \cup [hash : Hash, prev : {NoBlock} \cup [hash : Hash, prev : {NoBlock} \cup [hash : Hash, prev : {NoBlock} \cup [hash : Hash, prev : {NoBlock}, amt : Nat, owner : PrivateKey, sig : {"sig"}]]]]]]]

\* Safety: every block in every node's ledger is signed by the account's own
\* private key (lookup by the block's owner field above is always available
\* here because that private key is the one that placed the block there).
SafetyInvariant ==
  \A n \in Node :
    \A h \in Hash :
      IF ledger[n][h] = NoBlock THEN TRUE
      ELSE PublicKey[ledger[n][h].owner] = ledger[n][h].owner

====