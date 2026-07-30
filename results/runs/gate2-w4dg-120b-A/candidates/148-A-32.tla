---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
  CalculateHash, NoHash, NoBlock

\* Distributed ledger: a map from block hashes to signed blocks. Every node holds
\* its own copy, which is what makes validation order-dependent.
\* Hacked by Create* actions (which broadcast to all copies) and Process* actions
\* (which validate a received block before adding it to the local copy).
\* A block records the account chain it belongs to, the previous block in that
\* chain, and -- for send/receive blocks -- the other party and amount.
\* The lastHash state variable exists solely to feed the hash calculation
\* operator, and is never used by validation logic.
Variables == <<lastHash, ledger, received>>

Blocks == [hash: Hash, chain: PublicKey, prev: {NoHash} \union Hash,
           kind: {"genesis", "send", "open", "receive", "change"},
           to: {NoHash} \union PublicKey, amt: 0..GenesisBalance]

TypeOK ==
  /\ lastHash \in {NoHash} \union Hash
  /\ ledger \in [Node -> [Hash -> {NoBlockVal} \union Blocks]]
  /\ received \in [Node -> SUBSET {NoBlockVal} \union Blocks]

RECURSIVE ChainSum(_, _)
ChainSum(chain, h) ==
  IF h = NoHash THEN 0
  ELSE LET b == ledger[CHOOSE n \in Node : TRUE][h] IN
       IF b.kind = "receive" THEN b.amt + ChainSum(chain, b.prev) ELSE ChainSum(chain, b.prev)

RECURSIVE HasBlock(_, _, _)
HasBlock(chain, h, n) ==
  IF h = NoHash THEN FALSE
  ELSE LET b == ledger[n][h] IN (b.chain = chain \/ HasBlock(chain, b.prev, n))

OwnedPublic == {PublicKey[k] : k \in PrivateKey}
Balance(n) == ChainSum(PublicKey[n], LastHash(n))
LastHash(n) == CHOOSE h \in Hash : ledger[n][h] # NoBlockVal
AuthorOf(b) == CHOOSE k \in PrivateKey : PublicKey[k] = b.chain
ValidSignature(b) == AuthorOf(b) # NoHash
ReferredTo(n) == { h \in Hash :
  \/ ledger[n][h].kind = "send" \/ ledger[n][h].kind = "receive"
  \/ ledger[n][h].kind = "open" \/ ledger[n][h].kind = "change" }

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* Creating a genesis block is a broadcast that touches every node's copy at
\* once -- the single point where the ledger stops being empty.
CreateGenesis(n, k) ==
  /\ lastHash = NoHash
  /\ ledger = [m \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ LET b == [hash |-> NoHash, chain |-> PublicKey[k], prev |-> NoHash,
               kind |-> "genesis", to |-> NoHash, amt |-> GenesisBalance] IN
       /\ lastHash' = NoHashVal
       /\ ledger' = [m \in Node |-> [h \in Hash |-> IF h = NoHashVal THEN b ELSE NoBlockVal]]
       /\ received' = [m \in Node |-> {}]

CreateSend(n, to, amt) ==
  /\ lastHash # NoHash
  /\ Balance(n) >= amt /\ to \notin OwnedPublic
  /\ LET b == [hash |-> NoHash, chain |-> PublicKey[n], prev |-> lastHash,
               kind |-> "send", to |-> to, amt |-> amt] IN
       /\ lastHash' = NoHashVal
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![NoHashVal] = b]]
       /\ received' = [m \in Node |-> received[m] \union {b}]

CreateOpen(n, m) ==
  /\ lastHash # NoHash
  /\ ~HasBlock(PublicKey[n], lastHash, n)
  /\ LET b == [hash |-> NoHash, chain |-> PublicKey[n], prev |-> lastHash,
               kind |-> "open", to |-> NoHash, amt |-> 0] IN
       /\ lastHash' = NoHashVal
       /\ ledger' = [o \in Node |-> [ledger[o] EXCEPT ![NoHashVal] = b]]
       /\ received' = [o \in Node |-> received[o] \union {b}]

CreateReceive(n, m) ==
  /\ lastHash # NoHash
  /\ \E h \in ReferredTo(n) : ledger[n][h].kind = "send" /\ ledger[n][h].to = PublicKey[n]
  /\ LET b == [hash |-> NoHash, chain |-> PublicKey[n], prev |-> lastHash,
               kind |-> "receive", to |-> NoHash, amt |-> 0] IN
       /\ lastHash' = NoHashVal
       /\ ledger' = [o \in Node |-> [ledger[o] EXCEPT ![NoHashVal] = b]]
       /\ received' = [o \in Node |-> received[o] \union {b}]

CreateChange(n) ==
  /\ lastHash # NoHash
  /\ LET b == [hash |-> NoHash, chain |-> PublicKey[n], prev |-> lastHash,
               kind |-> "change", to |-> NoHash, amt |-> 0] IN
       /\ lastHash' = NoHashVal
       /\ ledger' = [o \in Node |-> [ledger[o] EXCEPT ![NoHashVal] = b]]
       /\ received' = [o \in Node |-> received[o] \union {b}]

\* Validation is the only place signatures and references get checked; a
\* broadcast block is merely sitting in the received set until someone validates it.
ValidateAccept(n, b) ==
  /\ b \in received[n]
  /\ ~ValidSignature(b) => FALSE
  /\ \/ b.kind = "send" => \A m \in Node : ledger[m][b.prev] # NoBlockVal /\ ledger[m][b.prev].chain = b.chain
     \/ b.kind = "receive" => \A m \in Node : ledger[m][b.prev] # NoBlockVal /\ ~\E p \in Hash : ledger[m][p].kind = "send" /\ ledger[m][p].to = b.chain
     \/ b.kind = "open" => \A m \in Node : ~\E p \in Hash : ledger[m][p].kind = "send" /\ ledger[m][p].to = b.chain
     \/ TRUE
  /\ ledger' = [ledger EXCEPT ![n][b.hash] = b]
  /\ received' = [received EXCEPT ![n] = @ \ {b}]
  /\ UNCHANGED lastHash

ValidateReject(n, b) ==
  /\ b \in received[n]
  /\ ~ValidSignature(b) \/ b.kind = "send" /\ Balance(n) < b.amt
  /\ received' = [received EXCEPT ![n] = @ \ {b}]
  /\ UNCHANGED <<lastHash, ledger>>

Next ==
  \/ \E n \in Node, k \in PrivateKey : CreateGenesis(n, k)
  \/ \E n \in Node, to \in PublicKey : CreateSend(n, to, 1)
  \/ \E n \in Node, m \in Node : CreateOpen(n, m)
  \/ \E n \in Node, m \in Node : CreateReceive(n, m)
  \/ \E n \in Node : CreateChange(n)
  \/ \E n \in Node, b \in {NoBlockVal} \union Blocks : ValidateAccept(n, b)
  \/ \E n \in Node, b \in {NoBlockVal} \union Blocks : ValidateReject(n, b)

Spec == Init /\ [][Next]_Variables

\* The only functional safety requirement: signatures must always check out.
SafetyInvariant == \A n \in Node, h \in Hash : ledger[n][h] # NoBlockVal => ValidSignature(ledger[n][h])

====