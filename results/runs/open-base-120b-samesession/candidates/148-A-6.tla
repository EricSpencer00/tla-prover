---- MODULE Nano ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Hash,
    NoHashVal,
    PrivateKey,
    PublicKey,
    Node,
    GenesisBalance,
    NoBlockVal,
    CalculateHash,
    NoHash,
    NoBlock

(* ---------------------------------------------------------------------- *)
(* Helper definitions (modeled abstractly)                               *)
(* ---------------------------------------------------------------------- *)

(* sentinel hash value *)
NoHash == NoHashVal

(* a dummy public key used for fields that are not relevant for a given block type *)
NoPublicKey == CHOOSE pk \in PublicKey : TRUE

(* mapping each private key to its public key – abstractly chosen *)
PrivateToPublic == [pk \in PrivateKey |-> CHOOSE pub \in PublicKey : TRUE]

(* each node owns exactly one private key – abstractly chosen *)
NodeKey == [n \in Node |-> CHOOSE pk \in PrivateKey : TRUE]

(* the genesis private key – abstractly chosen *)
GenesisPriv == CHOOSE pk \in PrivateKey : TRUE

(* ---------------------------------------------------------------------- *)
(* Block datatype and cryptographic primitives                           *)
(* ---------------------------------------------------------------------- *)

Sig == [priv : PrivateKey, blk : Block]

Block ==
    [type      : {"Genesis", "Send", "Open", "Receive", "Change"},
     prev      : Hash,
     account   : PublicKey,
     amount    : Nat,
     recipient : PublicKey,
     source    : Hash,
     rep       : PublicKey,
     sig       : Sig]

(* abstract hash calculation – the cfg will substitute CalculateHashImpl *)
CalculateHashImpl(data, prev) == CHOOSE h \in Hash : TRUE
CalculateHash(data, prev) == CalculateHashImpl(data, prev)

(* signing and verification (abstract) *)
Sign(priv, blk) == [priv |-> priv, blk |-> blk]

ValidSignature(b) ==
    \E priv \in PrivateKey :
        /\ PrivateToPublic[priv] = b.account
        /\ b.sig = Sign(priv, b)

(* ---------------------------------------------------------------------- *)
(* State variables                                                       *)
(* ---------------------------------------------------------------------- *)

VARIABLES
    lastHash,   \* the most recent block hash (or NoHashVal)
    blocks,     \* global map: hash -> Block (or NoBlockVal)
    ledger,     \* per‑node copy of validated blocks
    received    \* per‑node set of hashes awaiting validation

(* ---------------------------------------------------------------------- *)
(* Initial state                                                          *)
(* ---------------------------------------------------------------------- *)

Init ==
    /\ lastHash = NoHashVal
    /\ blocks   = [h \in Hash |-> NoBlockVal]
    /\ ledger   = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

(* ---------------------------------------------------------------------- *)
(* Validation of a received block                                         *)
(* ---------------------------------------------------------------------- *)

ValidateBlock(node, h) ==
    LET b == blocks[h] IN
        /\ b # NoBlockVal
        /\ ValidSignature(b)
        (* type‑specific checks could be added here *)

(* ---------------------------------------------------------------------- *)
(* Actions                                                               *)
(* ---------------------------------------------------------------------- *)

CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ LET b ==
            [type      |-> "Genesis",
             prev      |-> NoHash,
             account   |-> PrivateToPublic[GenesisPriv],
             amount    |-> GenesisBalance,
             recipient |-> NoPublicKey,
             source    |-> NoHash,
             rep       |-> NoPublicKey,
             sig       |-> Sign(GenesisPriv, <<>>)]
       newHash == CalculateHash(b, NoHash) IN
       /\ lastHash' = newHash
       /\ blocks'   = [blocks EXCEPT ![newHash] = b]
       /\ ledger'   = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
       /\ received' = [n \in Node |-> {newHash}]
    /\ UNCHANGED << >>

CreateSend(node, amount, recip) ==
    /\ node \in Node
    /\ amount \in Nat
    /\ recip \in PublicKey
    /\ LET priv == NodeKey[node]
           b    ==
            [type      |-> "Send",
             prev      |-> lastHash,
             account   |-> PrivateToPublic[priv],
             amount    |-> amount,
             recipient |-> recip,
             source    |-> NoHash,
             rep       |-> NoPublicKey,
             sig       |-> Sign(priv, <<>>)]
           newHash == CalculateHash(b, lastHash) IN
       /\ lastHash' = newHash
       /\ blocks'   = [blocks EXCEPT ![newHash] = b]
       /\ ledger'   = ledger
       /\ received' = [received EXCEPT ![node] = @ \cup {newHash}]
    /\ UNCHANGED << >>

CreateOpen(node, srcHash) ==
    /\ node \in Node
    /\ srcHash \in Hash
    /\ LET priv == NodeKey[node]
           b    ==
            [type      |-> "Open",
             prev      |-> NoHash,
             account   |-> PrivateToPublic[priv],
             amount    |-> 0,
             recipient |-> NoPublicKey,
             source    |-> srcHash,
             rep       |-> NoPublicKey,
             sig       |-> Sign(priv, <<>>)]
           newHash == CalculateHash(b, lastHash) IN
       /\ lastHash' = newHash
       /\ blocks'   = [blocks EXCEPT ![newHash] = b]
       /\ ledger'   = ledger
       /\ received' = [received EXCEPT ![node] = @ \cup {newHash}]
    /\ UNCHANGED << >>

CreateReceive(node, srcHash) ==
    /\ node \in Node
    /\ srcHash \in Hash
    /\ LET priv == NodeKey[node]
           b    ==
            [type      |-> "Receive",
             prev      |-> lastHash,
             account   |-> PrivateToPublic[priv],
             amount    |-> 0,
             recipient |-> NoPublicKey,
             source    |-> srcHash,
             rep       |-> NoPublicKey,
             sig       |-> Sign(priv, <<>>)]
           newHash == CalculateHash(b, lastHash) IN
       /\ lastHash' = newHash
       /\ blocks'   = [blocks EXCEPT ![newHash] = b]
       /\ ledger'   = ledger
       /\ received' = [received EXCEPT ![node] = @ \cup {newHash}]
    /\ UNCHANGED << >>

CreateChange(node, repKey) ==
    /\ node \in Node
    /\ repKey \in PublicKey
    /\ LET priv == NodeKey[node]
           b    ==
            [type      |-> "Change",
             prev      |-> lastHash,
             account   |-> PrivateToPublic[priv],
             amount    |-> 0,
             recipient |-> NoPublicKey,
             source    |-> NoHash,
             rep       |-> repKey,
             sig       |-> Sign(priv, <<>>)]
           newHash == CalculateHash(b, lastHash) IN
       /\ lastHash' = newHash
       /\ blocks'   = [blocks EXCEPT ![newHash] = b]
       /\ ledger'   = ledger
       /\ received' = [received EXCEPT ![node] = @ \cup {newHash}]
    /\ UNCHANGED << >>

ProcessBlock(node) ==
    /\ node \in Node
    /\ \E h \in received[node] :
          ValidateBlock(node, h)
          /\ /\ lastHash' = lastHash
              /\ blocks'   = blocks
              /\ ledger'   = [ledger EXCEPT ![node][h] = blocks[h]]
              /\ received' = [received EXCEPT ![node] = @ \ {h}]
    /\ UNCHANGED << >>

Next ==
    \/ CreateGenesis
    \/ \E n \in Node, a \in Nat, r \in PublicKey : CreateSend(n, a, r)
    \/ \E n \in Node, sh \in Hash           : CreateOpen(n, sh)
    \/ \E n \in Node, sh \in Hash           : CreateReceive(n, sh)
    \/ \E n \in Node, rp \in PublicKey      : CreateChange(n, rp)
    \/ \E n \in Node                        : ProcessBlock(n)

(* ---------------------------------------------------------------------- *)
(* Specification                                                          *)
(* ---------------------------------------------------------------------- *)

Spec ==
    Init /\ [][Next]_<<lastHash, blocks, ledger, received>>

(* ---------------------------------------------------------------------- *)
(* Invariants                                                             *)
(* ---------------------------------------------------------------------- *)

TypeInvariant ==
    /\ lastHash \in Hash
    /\ blocks   \in [Hash -> (Block \cup {NoBlockVal})]
    /\ ledger   \in [Node -> [Hash -> (Block \cup {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node, h \in Hash :
        /\ ledger[n][h] # NoBlockVal
        => ValidSignature(ledger[n][h])

====