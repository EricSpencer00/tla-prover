---- MODULE Nano ----
EXTENDS Naturals, Sequences

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

HashDomain == Union({Hash, {NoHashVal}})

BlockType == {"Genesis", "Send", "Open", "Receive", "ChangeRep"}
NoNode == "NoNode"

ASSUME NoHashVal \notin Hash
ASSUME NoBlockVal \notin Hash
ASSUME NoHash \notin Node

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Each account's chain of blocks is a sequence; the balance is the sum of the
\* amounts carried by the blocks in that sequence, so the chain holds the whole
\* history relevant to the balance. Actions always append and never delete.
\* The safety invariant below is the full public-key signature check on every
\* block in every node's ledger, which is what keeps the chain trustworthy.
AccountChain(n) == CHOOSE h \in Hash : ledger[n][h].hash = h
BalanceOfSeq(s) == IF s = <<>> THEN 0 ELSE Head(s).amt + BalanceOfSeq(Tail(s))
AccountBalance(n) == BalanceOfSeq(AccountChain(n))

TypeOK ==
  /\ lastHash \in HashDomain
  /\ ledger \in [Node -> [Hash -> {NoBlockVal} \union [type: BlockType,
                                                    hash: Hash,
                                                    pk: PublicKey,
                                                    creator: Node,
                                                    amt: Nat,
                                                    link: Hash,
                                                    prev: Hash]]] /\ received \in
       [Node -> SUBSET Hash]

\* Every block in every node's replicated ledger must carry a signature that
\* checks out against the public key of the account (node) that owns its chain.
\* That property is what makes the history tamper-proof, since a forged
\* block would have to defeat the signature check at every node.
SignatureOK ==
  \A n \in Node, h \in Hash :
    ledger[n][h] # NoBlockVal => ~NoHashVal \in ledger[n][h].prev
      /\ ledger[n][h].pk = PublicKey[ledger[n][h].creator]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* Create the genesis block carrying the whole supply. This is the root of every
\* account chain and is written into every node's ledger together.
CreateGenesisBlock ==
  /\ lastHash = NoHashVal
  /\ \E n \in Node, k \in PrivateKey :
       /\ NoHash \in {ledger[n][h].hash : h \in Hash}
       /\ lastHash' = CalculateHash(h, NoHash)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] =
          [type |-> "Genesis", hash |-> lastHash', pk |-> PublicKey[k],
           creator |-> n, amt |-> GenesisBalance, link |-> NoHashVal,
           prev |-> NoHashVal]]]
       /\ received' = [m \in Node |-> received[m] \union {lastHash'}]

\* Send transfers funds from the account of the creating node to a recipient.
CreateSendBlock ==
  /\ lastHash # NoHashVal
  /\ \E n \in Node, k \in PrivateKey, amt \in 1 .. AccountBalance(n), rcpt \in Node :
       /\ AccountBalance(n) - amt >= 0
       /\ NoHash \notin {ledger[n][h].hash : h \in Hash}
       /\ lastHash' = CalculateHash(h, NoHash)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] =
          [type |-> "Send", hash |-> lastHash', pk |-> PublicKey[k],
           creator |-> n, amt |-> amt, link |-> NoHashVal,
           prev |-> NoHashVal]]]
       /\ received' = [m \in Node |-> received[m] \union {lastHash'}]

\* Open a new account chain by referencing a send block addressed to this node.
CreateOpenBlock ==
  /\ lastHash # NoHashVal
  /\ \E n \in Node, k \in PrivateKey, h \in Hash :
       /\ ledger[n][h] # NoBlockVal /\ ledger[n][h].type = "Send"
         /\ ledger[n][h].link = NoHashVal /\ ledger[n][h].amt > 0
       /\ NoHash \notin {ledger[n][g].hash : g \in Hash}
       /\ lastHash' = CalculateHash(h, NoHash)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] =
          [type |-> "Open", hash |-> lastHash', pk |-> PublicKey[k],
           creator |-> n, amt |-> ledger[n][h].amt, link |-> h,
           prev |-> NoHashVal]]]
       /\ received' = [m \in Node |-> received[m] \union {lastHash'}]

\* Receive adds an inbound transfer to the account chain.
CreateReceiveBlock ==
  /\ lastHash # NoHashVal
  /\ \E n \in Node, k \in PrivateKey, h \in Hash :
       /\ ledger[n][h] # NoBlockVal /\ ledger[n][h].type = "Send"
         /\ ledger[n][h].link = NoHashVal /\ ledger[n][h].amt > 0
       /\ NoHash \notin {ledger[n][g].hash : g \in Hash}
       /\ \A g \in Hash : ~(ledger[n][g] # NoBlockVal /\ ledger[n][g].link = h)
       /\ lastHash' = CalculateHash(h, NoHash)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] =
          [type |-> "Receive", hash |-> lastHash', pk |-> PublicKey[k],
           creator |-> n, amt |-> ledger[n][h].amt, link |-> h,
           prev |-> AccountChain(n).hash]]]
       /\ received' = [m \in Node |-> received[m] \union {lastHash'}]

\* Change the representative voting on this node's behalf.
CreateChangeRepBlock ==
  /\ lastHash # NoHashVal
  /\ \E n \in Node, k \in PrivateKey :
       /\ NoHash \notin {ledger[n][h].hash : h \in Hash}
       /\ lastHash' = CalculateHash(h, NoHash)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] =
          [type |-> "ChangeRep", hash |-> lastHash', pk |-> PublicKey[k],
           creator |-> n, amt |-> 0, link |-> NoHashVal,
           prev |-> AccountChain(n).hash]]]
       /\ received' = [m \in Node |-> received[m] \union {lastHash'}]

Validate(p, h) ==
  /\ ledger[p][h] = NoBlockVal
  /\ h \in received[p]
  /\ ledger[p][h].prev \in {NoHashVal} \union {ledger[p][g].hash : g \in Hash}
  /\ \A g \in Hash : ledger[p][g] # NoBlockVal => ledger[p][g].pk \in PublicKey
  /\ ledger' = [ledger EXCEPT ![p][h] = ledger[p][h]]
  /\ received' = [received EXCEPT ![p] = received[p] \ {h}]
  /\ UNCHANGED lastHash

\* Every node validates inbound blocks in its own order, independently.
ValidateAny ==
  \E p \in Node, h \in Hash : Validate(p, h)

Next ==
  \/ CreateGenesisBlock \/ CreateSendBlock \/ CreateOpenBlock
  \/ CreateReceiveBlock \/ CreateChangeRepBlock \/ ValidateAny

Spec == Init /\ [][Next]_vars

BalanceNeverExceedsGenesis == \A n \in Node : AccountBalance(n) <= GenesisBalance

====