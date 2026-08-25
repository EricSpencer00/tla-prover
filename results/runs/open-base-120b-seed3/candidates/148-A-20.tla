---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Hash,            \* set of all possible hash values
    NoHashVal,       \* a distinguished value of Hash used as a sentinel
    PrivateKey,      \* set of private keys
    PublicKey,       \* set of public keys
    Node,            \* set of network nodes
    GenesisBalance,  \* total supply of coins (a natural number)
    NoBlockVal,      \* a distinguished sentinel value for blocks
    CalculateHash,   \* abstract hash calculation operator (overridden by cfg)
    NoHash,          \* synonym for NoHashVal (used in block records)
    NoBlock          \* synonym for NoBlockVal (used in ledgers)

\* ----------------------------------------------------------------------
\*  Derived constants / operators
\* ----------------------------------------------------------------------
CalculateHashImpl(hashData, prevHash) ==
    (* A concrete (finite) implementation of the hash function.
       The actual definition is left abstract; the cfg file will replace
       CalculateHash with this operator. *)
    CHOOSE h \in Hash : h # NoHash

\* Mapping from private keys to their corresponding public keys.
\* This is a constant function supplied by the configuration.
PubKeyOf == [pk \in PrivateKey |-> PublicKeyMap[pk]]

\* Mapping from nodes to the private key they own.
\* Also supplied as a constant (function) by the configuration.
NodePrivKey == [n \in Node |-> NodeKeyMap[n]]

\* ----------------------------------------------------------------------
\*  Record definition for a block
\* ----------------------------------------------------------------------
Block ==
    [ type          : {"genesis", "send", "open", "receive", "change"},
      prev          : Hash,
      account       : PublicKey,
      recipient     : PublicKey \cup {NoHash},
      amount        : Nat,
      signature     : Set    \* abstract representation of a signature
    ]

\* Sentinel values for hash and block
NoHash == NoHashVal
NoBlock == NoBlockVal

\* ----------------------------------------------------------------------
\*  State variables
\* ----------------------------------------------------------------------
VARIABLES
    LastHash,   \* the most recent hash that has been created (or NoHash)
    Ledger,     \* [node \in Node -> [hash \in Hash -> Block \cup {NoBlock}]]
    Received,   \* [node \in Node -> SUBSET Hash]   \* hashes pending validation
    Blocks      \* [hash \in Hash -> Block \cup {NoBlock}]  \* global pool of created blocks

\* ----------------------------------------------------------------------
\*  Helper functions
\* ----------------------------------------------------------------------
\* Sign a block using a private key (abstract)
Sign(pk, blk) == {pk, blk}   \* abstract representation

\* A block has a valid signature iff there exists a private key that maps to the
\* block's account public key and the signature matches Sign(pk, blk).
ValidSignature(blk) ==
    \E pk \in PrivateKey :
        PubKeyOf[pk] = blk.account /\ blk.signature = Sign(pk, blk)

\* Determine the balance of an account by walking its chain.
\* For brevity we provide an abstract definition used only in type checking.
Balance(pub) == 
    LET chain == { h \in Hash : 
                    \E n \in Node : Ledger[n][h] # NoBlock /\ Ledger[n][h].account = pub } 
    IN  IF chain = {} THEN 0 ELSE GenesisBalance   \* placeholder

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ LastHash = NoHash
    /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
    /\ Received = [n \in Node |-> {}]
    /\ Blocks = [h \in Hash |-> NoBlock]

\* ----------------------------------------------------------------------
\*  Actions
\* ----------------------------------------------------------------------
\* Helper to choose a fresh hash not already used.
FreshHash(new) ==
    /\ new \in Hash
    /\ new # NoHash
    /\ new \notin DOMAIN Blocks

\* Broadcast a newly created block to all nodes' Received sets.
Broadcast(newHash) ==
    [Received EXCEPT ![n \in Node] = @ [n] \cup {newHash}]

CreateGenesis ==
    /\ LastHash = NoHash        \* only once
    \E n \in Node :
        LET pk == PubKeyOf[NodePrivKey[n]] IN
        LET blk == [ type      |-> "genesis",
                     prev      |-> NoHash,
                     account   |-> pk,
                     recipient |-> NoHash,
                     amount    |-> GenesisBalance,
                     signature |-> Sign(NodePrivKey[n], "genesis") ] IN
        /\ FreshHash(newHash)
        /\ Blocks' = [Blocks EXCEPT ![newHash] = blk]
        /\ LastHash' = newHash
        /\ Ledger' = Ledger
        /\ Received' = Broadcast(newHash)
        /\ UNCHANGED << >>

CreateSend ==
    \E n \in Node, amt \in Nat :
        /\ amt <= Balance(PubKeyOf[NodePrivKey[n]])    \* cannot overdraw
        LET pk == PubKeyOf[NodePrivKey[n]] IN
        LET blk == [ type      |-> "send",
                     prev      |-> LastHash,
                     account   |-> pk,
                     recipient |-> NoHash,               \* to be filled by caller
                     amount    |-> amt,
                     signature |-> Sign(NodePrivKey[n], "send") ] IN
        /\ FreshHash(newHash)
        /\ Blocks' = [Blocks EXCEPT ![newHash] = blk]
        /\ LastHash' = newHash
        /\ Ledger' = Ledger
        /\ Received' = Broadcast(newHash)
        /\ UNCHANGED << >>

CreateOpen ==
    \E n \in Node, senderHash \in Hash :
        /\ Blocks[senderHash].type = "send"
        /\ Blocks[senderHash].recipient = PubKeyOf[NodePrivKey[n]]
        LET pk == PubKeyOf[NodePrivKey[n]] IN
        LET blk == [ type      |-> "open",
                     prev      |-> NoHash,
                     account   |-> pk,
                     recipient |-> NoHash,
                     amount    |-> Blocks[senderHash].amount,
                     signature |-> Sign(NodePrivKey[n], "open") ] IN
        /\ FreshHash(newHash)
        /\ Blocks' = [Blocks EXCEPT ![newHash] = blk]
        /\ LastHash' = newHash
        /\ Ledger' = Ledger
        /\ Received' = Broadcast(newHash)
        /\ UNCHANGED << >>

CreateReceive ==
    \E n \in Node, sendHash \in Hash :
        /\ Blocks[sendHash].type = "send"
        /\ Blocks[sendHash].recipient = PubKeyOf[NodePrivKey[n]]
        LET pk == PubKeyOf[NodePrivKey[n]] IN
        LET blk == [ type      |-> "receive",
                     prev      |-> LastHash,
                     account   |-> pk,
                     recipient |-> sendHash,
                     amount    |-> Blocks[sendHash].amount,
                     signature |-> Sign(NodePrivKey[n], "receive") ] IN
        /\ FreshHash(newHash)
        /\ Blocks' = [Blocks EXCEPT ![newHash] = blk]
        /\ LastHash' = newHash
        /\ Ledger' = Ledger
        /\ Received' = Broadcast(newHash)
        /\ UNCHANGED << >>

CreateChange ==
    \E n \in Node, newRep \in PublicKey :
        LET pk == PubKeyOf[NodePrivKey[n]] IN
        LET blk == [ type      |-> "change",
                     prev      |-> LastHash,
                     account   |-> pk,
                     recipient |-> newRep,
                     amount    |-> 0,
                     signature |-> Sign(NodePrivKey[n], "change") ] IN
        /\ FreshHash(newHash)
        /\ Blocks' = [Blocks EXCEPT ![newHash] = blk]
        /\ LastHash' = newHash
        /\ Ledger' = Ledger
        /\ Received' = Broadcast(newHash)
        /\ UNCHANGED << >>

ProcessBlock ==
    \E n \in Node, h \in Received[n] :
        LET blk == Blocks[h] IN
        /\ blk # NoBlock
        /\ ValidSignature(blk)          \* cryptographic check
        /\ Ledger' = [Ledger EXCEPT ![n][h] = blk]
        /\ Received' = [Received EXCEPT ![n] = @ \ {h}]
        /\ UNCHANGED << LastHash, Blocks >>

Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<LastHash, Ledger, Received, Blocks>>

\* ----------------------------------------------------------------------
\*  Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ LastHash \in Hash \cup {NoHash}
    /\ /\ \A n \in Node : Ledger[n] \in [Hash -> Block \cup {NoBlock}]
       /\ \A n \in Node : Received[n] \subseteq Hash
    /\ Blocks \in [Hash -> Block \cup {NoBlock}]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            /\ Ledger[n][h] # NoBlock
            => ValidSignature(Ledger[n][h])

\* ----------------------------------------------------------------------
\*  Declared identifiers for the configuration file
\* ----------------------------------------------------------------------
TypeInvariant == TypeInvariant
SafetyInvariant == SafetyInvariant
Spec == Spec
CalculateHashImpl == CalculateHashImpl

====