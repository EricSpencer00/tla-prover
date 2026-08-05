---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, received
vars == <<lastHash, ledger, received>>

\* An Ed25519 signature over the block hash signed by the account owner's private key.
\* A Blake2b hash over the block data is used as the block identifier, recorded in the
\* node's own chain so the chain order is itself a piece of order-sensitive state.
SignedBlock == [hash: Hash, owner: PublicKey, typ: {"genesis", "send", "open", "receive", "change"}, prev: Hash, target: PublicKey, amt: 0..GenesisBalance, sig: PrivateKey]

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> SignedBlock \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

\* The Ed25519 signature check: the signature must be the signer's private key and
\* the signer's public key must be the one registered to that private key.
SignatureValid(bl) == bl.sig = CHOOSE x \in PrivateKey : PublicKey[x] = bl.owner

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* The genesis block is the only block that can be created without a previous hash.
CreateGenesisBlock(n) ==
  /\ lastHash = NoHashVal
  /\ LET bl == [hash |-> CalculateHash("genesis", NoHash, NoHash, GenesisBalance), owner |-> PublicKey[n], typ |-> "genesis", prev |-> NoHash, target |-> NoHash, amt |-> GenesisBalance, sig |-> n]
     IN /\ ~ (\E h \in Hash : ledger[\A n \in Node |-> n][h] # NoBlockVal)
        /\ lastHash' = bl.hash
        /\ ledger' = [q \in Node |-> [ledger[q] EXCEPT ![bl.hash] = bl]]
        /\ received' = [q \in Node |-> received[q] \cup {bl.hash}]

CreateSendBlock(n, to, amt) ==
  /\ lastHash # NoHashVal
  /\ ledger[n][lastHash].owner = PublicKey[n]
  /\ amt > 0
  /\ LET bl == [hash |-> CalculateHash("send", lastHash, to, amt), owner |-> PublicKey[n], typ |-> "send", prev |-> lastHash, target |-> to, amt |-> amt, sig |-> n]
     IN /\ bl.amt <= Balance(n, lastHash)
        /\ lastHash' = bl.hash
        /\ ledger' = [q \in Node |-> [ledger[q] EXCEPT ![bl.hash] = bl]]
        /\ received' = [q \in Node |-> received[q] \cup {bl.hash}]

CreateOpenBlock(n, sendHash) ==
  /\ lastHash # NoHashVal
  /\ sendHash \in Hash
  /\ ledger[n][sendHash].typ = "send"
  /\ ledger[n][sendHash].target = PublicKey[n]
  /\ ~ (\E h \in Hash : ledger[n][h].typ = "open")
  /\ LET bl == [hash |-> CalculateHash("open", lastHash, NoHash, 0), owner |-> PublicKey[n], typ |-> "open", prev |-> lastHash, target |-> NoHash, amt |-> 0, sig |-> n]
     IN /\ lastHash' = bl.hash
        /\ ledger' = [q \in Node |-> [ledger[q] EXCEPT ![bl.hash] = bl]]
        /\ received' = [q \in Node |-> received[q] \cup {bl.hash}]

CreateReceiveBlock(n, recvHash, sendHash) ==
  /\ lastHash # NoHashVal
  /\ recvHash \in Hash
  /\ sendHash \in Hash
  /\ ledger[n][recvHash].typ = "open"
  /\ ledger[n][sendHash].typ = "send"
  /\ ledger[n][sendHash].target = PublicKey[n]
  /\ ~ (\E h \in Hash : ledger[n][h].typ = "receive" /\ ledger[n][h].target = sendHash)
  /\ LET bl == [hash |-> CalculateHash("receive", recvHash, sendHash, ledger[n][sendHash].amt), owner |-> PublicKey[n], typ |-> "receive", prev |-> recvHash, target |-> sendHash, amt |-> ledger[n][sendHash].amt, sig |-> n]
     IN /\ lastHash' = bl.hash
        /\ ledger' = [q \in Node |-> [ledger[q] EXCEPT ![bl.hash] = bl]]
        /\ received' = [q \in Node |-> received[q] \cup {bl.hash}]

CreateChangeBlock(n, rep) ==
  /\ lastHash # NoHashVal
  /\ LET bl == [hash |-> CalculateHash("change", lastHash, NoHash, 0), owner |-> PublicKey[n], typ |-> "change", prev |-> lastHash, target |-> rep, amt |-> 0, sig |-> n]
     IN /\ lastHash' = bl.hash
        /\ ledger' = [q \in Node |-> [ledger[q] EXCEPT ![bl.hash] = bl]]
        /\ received' = [q \in Node |-> received[q] \cup {bl.hash}]

\* Each receiver validates the block against its own copy of the ledger (the
\* sender may be slow but is never assumed to be maliciously faulty).
ValidateBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] # NoBlockVal
  /\ SignatureValid(ledger[n][h])
  /\ ledger' = [q \in Node |-> [ledger[q] EXCEPT ![h] = ledger[n][h]]]
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node : CreateGenesisBlock(n)
  \/ \E n \in Node, to \in PublicKey, amt \in 1..GenesisBalance : CreateSendBlock(n, to, amt)
  \/ \E n \in Node, h \in Hash : CreateOpenBlock(n, h)
  \/ \E n \in Node, h \in Hash, g \in Hash : CreateReceiveBlock(n, h, g)
  \/ \E n \in Node, rep \in PublicKey : CreateChangeBlock(n, rep)
  \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

\* Safety: every block in every node's ledger has a signature that actually
\* belongs to the account owning the block's chain -- no forged block ever lands
\* in the replicated ledger.
SafetyInvariant ==
  \A n \in Node : \A h \in Hash :
    ledger[n][h] # NoBlockVal => ledger[n][h].owner = PublicKey[ledger[n][h].sig]

====