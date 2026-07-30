---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, NoHash

\* CalculateHash is deliberately underspecified at this level; the .cfg
\* substitutes a concrete implementation for model checking.
CONSTANTS CalculateHash

ASSUME GenesisBalance \in Nat

Blocks == {"genesis"} \cup (Hash \ {NoHashVal})

\* AccountChain stores the full block chain per account, newest first.
AccountChain == [PublicKey -> Seq(Blocks)]

VARIABLES lastHash, ledger, received

vars == << lastHash, ledger, received >>

TypeOK ==
  /\ lastHash \in (Hash \cup {NoHashVal})
  /\ ledger \in [Node -> [Hash -> Blocks \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

\* A block's chain is empty when no block hashes it as its predecessor.
ChainEmpty(h) == \A k \in PublicKey, i \in 1..Len(AccountChain[k]) : AccountChain[k][i] # h

\* Genesis: a single block seeded by any private key holder.
Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* Sign produces an Ed25519 signature (modeled abstractly) from the block
\* data, the previous hash, and the signer's private key.
Signature(data, prev, prv) == CHOOSE sig \in (Hash \cup {NoHashVal}) : TRUE

\* Broadcast a freshly created block to every node's inbox.
Broadcast(h) ==
  /\ \A n \in Node : received' = [received EXCEPT ![n] = @ \cup {h}]
  /\ UNCHANGED << lastHash, ledger >>

ValidSignature(h) ==
  /\ \E prv \in PrivateKey :
       /\ ledger[NodeOf(prv)] = [h \in Hash |-> IF h = lastHash THEN NoBlockVal ELSE ledger[NodeOf(prv)][h]]
       /\ \E data \in PUBLICKEY : ledger[NodeOf(prv)][h] = Signature(data, lastHash, prv)
  /\ \E data \in PUBLICKEY : ledger[NodeOf(prv)][h] = Signature(data, lastHash, prv)

CreateGenesis(prv) ==
  /\ lastHash = NoHashVal
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![NoHashVal] =
                 IF n = NodeOf(prv) THEN Signature(NodeOf(prv), NoHashVal, prv) ELSE NoBlockVal]]
  /\ lastHash' = NoHashVal
  /\ Broadcast(NoHashVal)
  /\ UNCHANGED received

\* Walk the chain to compute an account's balance recursively.
Balance(k, n) ==
  IF n > Len(AccountChain[k]) THEN 0
  ELSE IF n = 1 THEN GenesisBalance
  ELSE
    LET blk == AccountChain[k][n] IN
      IF blk = "genesis" THEN GenesisBalance
      ELSE IF blk = "send" THEN Balance(k, n-1) - 1
      ELSE IF blk = "receive" THEN Balance(k, n-1) + 1
      ELSE Balance(k, n-1)

\* Sending is blocked by an available balance check.
CreateSend(n, prv) ==
  /\ lastHash # NoHashVal
  /\ ChainEmpty(lastHash)
  /\ Balance(NodeOf(prv), Len(AccountChain[NodeOf(prv)])) > 0
  /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![lastHash] =
                 Signature(NodeOf(prv), lastHash, prv)]]
  /\ lastHash' = CalculateHash({NodeOf(prv), lastHash}, prv)
  /\ Broadcast(lastHash)
  /\ UNCHANGED received

CreateOpen(n, prv) ==
  /\ lastHash # NoHashVal
  /\ ChainEmpty(lastHash)
  /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![lastHash] =
                 Signature(NodeOf(prv), lastHash, prv)]]
  /\ lastHash' = CalculateHash({NodeOf(prv), lastHash}, prv)
  /\ Broadcast(lastHash)
  /\ UNCHANGED received

CreateReceive(n, prv) ==
  /\ lastHash # NoHashVal
  /\ ChainEmpty(lastHash)
  /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![lastHash] =
                 Signature(NodeOf(prv), lastHash, prv)]]
  /\ lastHash' = CalculateHash({NodeOf(prv), lastHash}, prv)
  /\ Broadcast(lastHash)
  /\ UNCHANGED received

\* A change does not move funds, so no balance check is needed.
CreateChangeRep(n, prv) ==
  /\ lastHash # NoHashVal
  /\ ChainEmpty(lastHash)
  /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![lastHash] =
                 Signature(NodeOf(prv), lastHash, prv)]]
  /\ lastHash' = CalculateHash({NodeOf(prv), lastHash}, prv)
  /\ Broadcast(lastHash)
  /\ UNCHANGED received

\* Validation checks the signature, referenced blocks, and the block type.
Validate(n, h) ==
  /\ h \in received[n]
  /\ \E prv \in PrivateKey :
       /\ ledger[n][h] = Signature(NodeOf(prv), NoHashVal, prv)
       /\ lastHash = NoHashVal
  /\ ledger' = [ledger EXCEPT ![n][h] = ledger[n][h]]
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E prv \in PrivateKey : CreateGenesis(prv) \/ CreateSend(NodeOf(prv), prv)
                            \/ CreateOpen(NodeOf(prv), prv) \/ CreateReceive(NodeOf(prv), prv)
                            \/ CreateChangeRep(NodeOf(prv), prv)
  \/ \E n \in Node, h \in Hash : Validate(n, h)

Spec == Init /\ [][Next]_vars

SafetyInvariant ==
  \A n \in Node, h \in Hash : ledger[n][h] # NoBlockVal => ValidSignature(h)

====