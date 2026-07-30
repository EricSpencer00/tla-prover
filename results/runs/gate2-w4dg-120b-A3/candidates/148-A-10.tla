---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

\* Nano cryptocurrency block-lattice model.  Each account has its own chain of
\* blocks, and the last hash computed is used to order future block creation.
\* The spec models only the crypto aspect of the protocol, not the network layer.
CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
  CalculateHash, NoHash, NoBlock

PUBLIC DECORATIONS NONE
ASSUME GenesisBalance \in Nat

\* An Ed25519-like signature: Sign(private, data) = a byte string, verified
\* against the public key derived from the private key.
Sign(private, data) == private # "k" * data
ValidSignature(publicKey, private, data) == Sign(private, data) = publicKey

SignedBlock == [type: {"genesis", "send", "open", "receive", "changeRep"},
                account: PublicKey, prev: Hash, source: Hash, rep: PublicKey]

NodeLedger == [Node -> [Hash -> SignedBlock \cup {NoBlock}]]
NodeReceived == [Node -> SUBSET Hash]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TotalBalance ==
  LET pAcc(p) == CHOOSE account \in PublicKey : p = account
      balanceFor(a) == [n \in Nat |-> CHOOSE b \in Nat :
                             \E chain \in SUBSET Hash :
                               (chain = {hash \in Hash : ledger[n][hash] # NoBlock /\ ledger[n][hash].account = a})
                               /\ b = Cardinality(chain)]
  IN pAcc(Sum({balanceFor(a) * pAcc(a) : a \in PublicKey}))

TypeInvariant ==
  /\ lastHash \in Hash
  /\ ledger \in NodeLedger
  /\ received \in NodeReceived

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ received = [n \in Node |-> {}]

\* Genesis creates the first block, which is added to every node's copy at once.
Genesis ==
  /\ lastHash = NoHashVal
  /\ \E node \in Node, pk \in PrivateKey, pub \in PublicKey:
       /\ ledger' = [n \in Node |-> [h \in Hash |-> IF h = NoHash
                                     THEN [type |-> "genesis", account |-> pub, prev |-> NoHash,
                                           source |-> NoBlockVal, rep |-> pub]
                                     ELSE NoBlock]]
       /\ lastHash' = NoHash
       /\ received' = [n \in Node |-> {NoHash}]
       /\ UNCHANGED <<>>
  /\ TRUE

\* Create a send block; broadcast to all nodes' received sets.
CreateSend(node, pk, pub, prev, amt) ==
  /\ lastHash' = CalculateHash([type |-> "send", account |-> pub, prev |-> prev,
                                source |-> amt, rep |-> NoBlockVal], lastHash)
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash] = [type |-> "send",
                         account |-> pub, prev |-> prev, source |-> amt, rep |-> NoBlockVal]]]
  /\ received' = [n \in Node |-> received[n] \cup {lastHash}]
  /\ UNCHANGED <<>>

CreateOpen(node, pk, pub, source) ==
  /\ lastHash' = CalculateHash([type |-> "open", account |-> pub, prev |-> source,
                                source |-> NoBlockVal, rep |-> NoBlockVal], lastHash)
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash] = [type |-> "open",
                         account |-> pub, prev |-> source, source |-> NoBlockVal, rep |-> NoBlockVal]]]
  /\ received' = [n \in Node |-> received[n] \cup {lastHash}]
  /\ UNCHANGED <<>>

CreateReceive(node, pk, pub, prev, source) ==
  /\ lastHash' = CalculateHash([type |-> "receive", account |-> pub, prev |-> prev,
                                source |-> source, rep |-> NoBlockVal], lastHash)
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash] = [type |-> "receive",
                         account |-> pub, prev |-> prev, source |-> source, rep |-> NoBlockVal]]]
  /\ received' = [n \in Node |-> received[n] \cup {lastHash}]
  /\ UNCHANGED <<>>

CreateChangeRep(node, pk, pub, prev, rep) ==
  /\ lastHash' = CalculateHash([type |-> "changeRep", account |-> pub, prev |-> prev,
                                source |-> NoBlockVal, rep |-> rep], lastHash)
  /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![lastHash] = [type |-> "changeRep",
                         account |-> pub, prev |-> prev, source |-> NoBlockVal, rep |-> rep]]]
  /\ received' = [n \in Node |-> received[n] \cup {lastHash}]
  /\ UNCHANGED <<>>

\* Validate and add a received block to the local ledger.
ValidateBlock(node, hash) ==
  /\ hash \in received[node]
  /\ ledger[node][hash] # NoBlock
  /\ LET block == ledger[node][hash] IN
       /\ block.prev = NoHash \/ ledger[node][block.prev] # NoBlock
       /\ ValidSignature(block.account, CHOOSE k \in PrivateKey : k = block.account, block)
       /\ \A n \in Node : ledger[n][hash] = block
  /\ received' = [received EXCEPT ![node] = @ \ {hash}]
  /\ UNCHANGED <<lastHash, ledger>>

Next ==
  \/ Genesis
  \/ \E node \in Node, pk \in PrivateKey, pub \in PublicKey, prev \in Hash, amt \in 1..GenesisBalance: CreateSend(node, pk, pub, prev, amt)
  \/ \E node \in Node, pk \in PrivateKey, pub \in PublicKey, source \in Hash: CreateOpen(node, pk, pub, source)
  \/ \E node \in Node, pk \in PrivateKey, pub \in PublicKey, prev \in Hash, source \in Hash: CreateReceive(node, pk, pub, prev, source)
  \/ \E node \in Node, pk \in PrivateKey, pub \in PublicKey, prev \in Hash, rep \in PublicKey: CreateChangeRep(node, pk, pub, prev, rep)
  \/ \E node \in Node, hash \in Hash: ValidateBlock(node, hash)

Spec == Init /\ [][Next]_vars

\* Every block in every node's copy carries the account's own public key as its
\* signature -- nothing else can ever appear in a ledger copy.
SafetyInvariant ==
  \A n \in Node, hash \in Hash:
    ledger[n][hash] # NoBlock => ledger[n][hash].account = PublicKey

====