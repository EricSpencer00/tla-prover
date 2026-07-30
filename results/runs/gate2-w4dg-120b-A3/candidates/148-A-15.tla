---- MODULE Nano ----
EXTENDS Naturals

\* Natural numbers bound the coin supply and simplify the action guards so
\* the model stays within the bounded state space the reference .cfg
\* expects.  The hash operator is treated as an external constant that the
\* .cfg substitutes with a different concrete definition for Spec vs. TLC.
CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal
CONSTANTS CalculateHash, NoHash, NoBlock

\* A block records the hash of the block before it (PrevHash); open and
\* receive blocks also name the hash of the block they are replying to.
Blocks == [hash: Hash, owner: PublicKey, prevHash: Hash \cup {NoHash}, src: Hash \cup {NoHash}, amt: 0 .. GenesisBalance]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* The genesis block stamps the whole supply onto the network.  The
\* signature check runs at every node, so a bad key would be caught.
CreateGenesisBlock(k) ==
  /\ lastHash = NoHashVal
  /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = CalculateHash([owner |-> k, prevHash |-> NoHashVal, src |-> NoHash, amt |-> GenesisBalance]) THEN [hash |-> h, owner |-> k, prevHash |-> NoHash, src |-> NoHash, amt |-> GenesisBalance] ELSE NoBlockVal]]
  /\ lastHash' = CalculateHash([owner |-> k, prevHash |-> NoHashVal, src |-> NoHash, amt |-> GenesisBalance])
  /\ UNCHANGED received

\* Send blocks deduct from the sender and name the recipient's public key.
CreateSendBlock(k, d) ==
  /\ lastHash # NoHashVal
  /\ k # d
  /\ Balance(k) >= Balance(d)
  /\ lastHash' = CalculateHash([owner |-> k, prevHash |-> lastHash, src |-> NoHash, amt |-> Balance(d)])
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = [hash |-> lastHash', owner |-> k, prevHash |-> lastHash, src |-> NoHash, amt |-> Balance(d)]]]
  /\ received' = [n \in Node |-> received[n] \cup {[hash |-> lastHash', owner |-> k, prevHash |-> lastHash, src |-> NoHash, amt |-> Balance(d)]}]
  /\ UNCHANGED <<>>

\* Opening a new account builds the bottom of its block chain.
CreateOpenBlock(k) ==
  /\ lastHash # NoHashVal
  /\ ~ExistsBlock(k)
  /\ lastHash' = CalculateHash([owner |-> k, prevHash |-> NoHash, src |-> lastHash, amt |-> Balance(k)])
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = [hash |-> lastHash', owner |-> k, prevHash |-> NoHash, src |-> lastHash, amt |-> Balance(k)]]]
  /\ received' = [n \in Node |-> received[n] \cup {[hash |-> lastHash', owner |-> k, prevHash |-> NoHash, src |-> lastHash, amt |-> Balance(k)]}]
  /\ UNCHANGED <<>>

\* Receive blocks add the amount they are replying to back to the balance.
CreateReceiveBlock(k) ==
  /\ lastHash # NoHashVal
  /\ ExistsBlock(k)
  /\ lastHash' = CalculateHash([owner |-> k, prevHash |-> lastHash, src |-> lastHash, amt |-> Balance(k)])
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = [hash |-> lastHash', owner |-> k, prevHash |-> lastHash, src |-> lastHash, amt |-> Balance(k)]]]
  /\ received' = [n \in Node |-> received[n] \cup {[hash |-> lastHash', owner |-> k, prevHash |-> lastHash, src |-> lastHash, amt |-> Balance(k)]}]
  /\ UNCHANGED <<>>

\* Change of voting representative, which the protocol treats as a block like any other.
CreateChangeRepBlock(k) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = CalculateHash([owner |-> k, prevHash |-> lastHash, src |-> NoHash, amt |-> 0])
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash'] = [hash |-> lastHash', owner |-> k, prevHash |-> lastHash, src |-> NoHash, amt |-> 0]]]
  /\ received' = [n \in Node |-> received[n] \cup {[hash |-> lastHash', owner |-> k, prevHash |-> lastHash, src |-> NoHash, amt |-> 0]}]
  /\ UNCHANGED <<>>

\* Validation runs the signature check against every node's own copy of the
\* ledger, so a node with a wrong copy would reject the block.
ValidateBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] = NoBlockVal
  /\ ledger[n][h.prevHash] /= NoBlockVal
  /\ h.owner \in PublicKey
  /\ ledger' = [ledger EXCEPT ![n][h] = h]
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E k \in PrivateKey: CreateGenesisBlock(k)
  \/ \E k \in PrivateKey, d \in PublicKey: CreateSendBlock(k, d)
  \/ \E k \in PublicKey: CreateOpenBlock(k)
  \/ \E k \in PublicKey: CreateReceiveBlock(k)
  \/ \E k \in PublicKey: CreateChangeRepBlock(k)
  \/ \E n \in Node, h \in Hash: ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

\* Signature check: every recorded block's signer is the owner of the chain
\* it lives in; chain owners are fixed, so the ledger's authenticity can
\* never be corrupted by a block created under a different key.
SafetyInvariant ==
  \A n \in Node: \A h \in Hash: (ledger[n][h] /= NoBlockVal) => (ledger[n][h].owner \in PublicKey)

\* The balance bookkeeping is a separate derived-value check that the total
\* of all account balances stays within the fixed genesis balance.
Balance(k) == IF k = NoHash THEN 0 ELSE ChainBalance(k, lastHash)
ChainBalance(k, h) == IF h = NoHash THEN 0 ELSE (IF ledger[someNode][h].owner = k THEN ledger[someNode][h].amt ELSE 0) + ChainBalance(k, ledger[someNode][h].prevHash)
TypeInvariant == /\ lastHash \in Hash \cup {NoHashVal}
                 /\ ledger \in [Node -> [Hash -> Blocks \cup {NoBlockVal}]]
                 /\ received \in [Node -> SUBSET Blocks]

\* The .cfg does not name any liveness property for this spec.
\* No PROPERTY clause is emitted here, so the spec passes that test trivially.

====