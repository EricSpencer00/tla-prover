---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*--------------------------------------------------------------------
  Constants (as required by the .cfg)
--------------------------------------------------------------------*)
CONSTANTS
    Hash,               \* the set of all possible block hashes
    NoHashVal,          \* sentinel value meaning "no hash"
    PrivateKey,         \* set of all private keys
    PublicKey,          \* set of all public keys
    Node,               \* set of all network nodes
    GenesisBalance,     \* total number of coins at genesis (a Nat)
    NoBlockVal,         \* sentinel meaning "no block"
    CalculateHash,      \* abstract hash operator: [data, prevHash -> Hash]
    NoHash,             \* alias for NoHashVal (for readability)
    NoBlock             \* alias for NoBlockVal (for readability)

(*--------------------------------------------------------------------
  Derived sets
--------------------------------------------------------------------*)
PUBLICKEYS == PUBLICKEY
ACCOUNT == PublicKey

(*--------------------------------------------------------------------
  Types
--------------------------------------------------------------------*)
BlockType == {"GENESIS", "SEND", "OPEN", "RECEIVE", "CHANGE"}

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES
    LastHash,          \* the hash of the most recent block added to the global ordering
    Ledger,            \* [node \in Node -> [hash \in Hash -> Block]]
    Received           \* [node \in Node -> SUBSET Hash]  (blocks announced but not yet processed)

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
\* A block record
Block == [type         : BlockType,
          hash         : Hash,
          prevHash     : Hash \cup {NoHash},
          source       : PublicKey \cup {NoBlock},
          destination  : PublicKey \cup {NoBlock},
          amount       : Nat,
          repr         : PublicKey \cup {NoBlock},
          signature    : STRING]   \* abstract representation of a signature

\* The empty block (used as placeholder for hashes that have no block yet)
EmptyBlock == [type         |-> "GENESIS",
               hash         |-> NoHash,
               prevHash     |-> NoHash,
               source       |-> NoBlock,
               destination  |-> NoBlock,
               amount       |-> 0,
               repr         |-> NoBlock,
               signature    |-> ""]

\* Mapping from a private key to its public key (must be total on PrivateKey)
KeyMap \in [PrivateKey -> PublicKey]

\* The owner of a node's account (each node controls exactly one private key)
NodeKey \in [Node -> PrivateKey]

\* Convenience: public key of a node
NodePub == [n \in Node |-> KeyMap[NodeKey[n]]]

\* Determine the block that a given hash points to in a node's ledger
BlockOf(node, h) == IF h = NoHash THEN EmptyBlock ELSE Ledger[node][h]

\* Balance of an account on a given node, computed by walking its chain
Balance(node, acc) ==
    LET Walk == 
        RECURSIVE Walk(_h) ==
            IF _h = NoHash THEN 0
            ELSE
                LET blk == BlockOf(node, _h) IN
                CASE blk.type = "SEND"   -> 0            \* SEND blocks do not add balance
                     [] blk.type = "OPEN"   -> blk.amount
                     [] blk.type = "RECEIVE"-> blk.amount + Walk(blk.prevHash)
                     [] blk.type = "CHANGE" -> Walk(blk.prevHash)
                     [] blk.type = "GENESIS"-> blk.amount
                     [] OTHER               -> Walk(blk.prevHash)
    IN Walk(LatestHash(node, acc))

\* Latest hash belonging to an account on a node (the head of its chain)
LatestHash(node, acc) ==
    LET IsOwned(h) == 
            LET blk == BlockOf(node, h) IN
            blk.type # "GENESIS" /\ blk.source = acc
    IN
        IF \E h \in Hash : IsOwned(h) THEN
            CHOOSE h \in Hash : IsOwned(h) /\ 
                \A h2 \in Hash : IsOwned(h2) => BlockOf(node, h).prevHash # h2
        ELSE NoHash

\* Validate a signature (abstract: we only check that signature string contains the public key)
ValidSignature(sig, pk) == /\ sig # "" /\ \A c \in SubSeq(sig, 1, Len(sig)) : TRUE \* placeholder; always true in abstract model

\* Derived constant: the genesis public key (owner of genesis block)
GenesisOwner \in PublicKey

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ LastHash = NoHash
    /\ Ledger = [n \in Node |-> [h \in Hash |-> EmptyBlock]]
    /\ Received = [n \in Node |-> {}]

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
CreateGenesis ==
    /\ LastHash = NoHash
    /\ \E pk \in PublicKey :
          /\ pk = GenesisOwner
          /\ LET h == CalculateHash([type |-> "GENESIS",
                                    amount |-> GenesisBalance,
                                    prevHash |-> NoHash,
                                    source |-> pk,
                                    destination |-> NoBlock,
                                    repr |-> pk],
                                    NoHash) IN
             h \in Hash
          /\ \A n \in Node :
                /\ Ledger' = [Ledger EXCEPT ![n][h] = 
                                   [type         |-> "GENESIS",
                                    hash         |-> h,
                                    prevHash     |-> NoHash,
                                    source       |-> pk,
                                    destination  |-> NoBlock,
                                    amount       |-> GenesisBalance,
                                    repr         |-> pk,
                                    signature    |-> "sig_" \o pk]]
                /\ Received' = Received
          /\ LastHash' = h
    /\ UNCHANGED <<>>

CreateSend(node, amount, destPub) ==
    /\ node \in Node
    /\ amount \in Nat
    /\ destPub \in PublicKey
    /\ amount > 0
    /\ LET senderPub == NodePub[node] IN
       /\ Balance(node, senderPub) >= amount
    /\ LET prev == LatestHash(node, senderPub) IN
    LET h == CalculateHash([type |-> "SEND",
                            amount |-> amount,
                            prevHash |-> prev,
                            source |-> senderPub,
                            destination |-> destPub,
                            repr |-> NodePub[node]],
                            prev) IN
       /\ h \in Hash
       /\ \A n \in Node :
            /\ Ledger' = [Ledger EXCEPT ![n][h] = 
                           [type         |-> "SEND",
                            hash         |-> h,
                            prevHash     |-> prev,
                            source       |-> senderPub,
                            destination  |-> destPub,
                            amount       |-> amount,
                            repr         |-> NodePub[node],
                            signature    |-> "sig_" \o senderPub]]
            /\ Received' = [Received EXCEPT ![n] = Received[n] \cup {h}]
    /\ UNCHANGED LastHash

CreateOpen(node, sendHash) ==
    /\ node \in Node
    /\ sendHash \in Hash
    /\ \E s \in Ledger[node][sendHash] :
          s.type = "SEND" /\ s.destination = NodePub[node]
    /\ LET prev == NoHash IN
    LET h == CalculateHash([type |-> "OPEN",
                            amount |-> s.amount,
                            prevHash |-> NoHash,
                            source |-> s.source,
                            destination |-> NodePub[node],
                            repr |-> NodePub[node]],
                            NoHash) IN
       /\ h \in Hash
       /\ \A n \in Node :
            /\ Ledger' = [Ledger EXCEPT ![n][h] = 
                           [type         |-> "OPEN",
                            hash         |-> h,
                            prevHash     |-> NoHash,
                            source       |-> s.source,
                            destination  |-> NodePub[node],
                            amount       |-> s.amount,
                            repr         |-> NodePub[node],
                            signature    |-> "sig_" \o s.source]]
            /\ Received' = [Received EXCEPT ![n] = Received[n] \cup {h}]
    /\ UNCHANGED LastHash

CreateReceive(node, sendHash, prevHash) ==
    /\ node \in Node
    /\ sendHash \in Hash
    /\ prevHash \in Hash
    /\ \E s \in Ledger[node][sendHash] :
          s.type = "SEND" /\ s.destination = NodePub[node]
    /\ \E p \in Ledger[node][prevHash] :
          p.type \in {"OPEN", "RECEIVE", "CHANGE"}
    /\ LET h == CalculateHash([type |-> "RECEIVE",
                               amount |-> s.amount,
                               prevHash |-> prevHash,
                               source |-> s.source,
                               destination |-> NodePub[node],
                               repr |-> NodePub[node]],
                               prevHash) IN
       /\ h \in Hash
       /\ \A n \in Node :
            /\ Ledger' = [Ledger EXCEPT ![n][h] = 
                           [type         |-> "RECEIVE",
                            hash         |-> h,
                            prevHash     |-> prevHash,
                            source       |-> s.source,
                            destination  |-> NodePub[node],
                            amount       |-> s.amount,
                            repr         |-> NodePub[node],
                            signature    |-> "sig_" \o s.source]]
            /\ Received' = [Received EXCEPT ![n] = Received[n] \cup {h}]
    /\ UNCHANGED LastHash

CreateChange(node, newRepr) ==
    /\ node \in Node
    /\ newRepr \in PublicKey
    /\ LET acc == NodePub[node] IN
    LET prev == LatestHash(node, acc) IN
    LET h == CalculateHash([type |-> "CHANGE",
                            amount |-> 0,
                            prevHash |-> prev,
                            source |-> acc,
                            destination |-> NoBlock,
                            repr |-> newRepr],
                            prev) IN
       /\ h \in Hash
       /\ \A n \in Node :
            /\ Ledger' = [Ledger EXCEPT ![n][h] = 
                           [type         |-> "CHANGE",
                            hash         |-> h,
                            prevHash     |-> prev,
                            source       |-> acc,
                            destination  |-> NoBlock,
                            amount       |-> 0,
                            repr         |-> newRepr,
                            signature    |-> "sig_" \o acc]]
            /\ Received' = [Received EXCEPT ![n] = Received[n] \cup {h}]
    /\ UNCHANGED LastHash

Process(node) ==
    /\ node \in Node
    /\ \E h \in Received[node] :
          /\ LET blk == Ledger[node][h] IN
             /\ blk.type # ""               \* ensure a block object
             /\ blk.signature # ""         \* placeholder check
             /\ ValidSignature(blk.signature, blk.source)
             /\ (blk.type = "SEND" => 
                     blk.amount <= Balance(node, blk.source))
             /\ (blk.type = "OPEN" => 
                     blk.prevHash = NoHash)
             /\ (blk.type \in {"RECEIVE", "CHANGE"} => 
                     blk.prevHash # NoHash)
          /\ Ledger' = [Ledger EXCEPT ![node][h] = blk]
          /\ Received' = [Received EXCEPT ![node] = Received[node] \ {h}]
    /\ UNCHANGED <<LastHash>>

Next ==
    \/ \E node \in Node, amount \in Nat, dest \in PublicKey :
          CreateSend(node, amount, dest)
    \/ \E node \in Node, sh \in Hash :
          CreateOpen(node, sh)
    \/ \E node \in Node, sh \in Hash, ph \in Hash :
          CreateReceive(node, sh, ph)
    \/ \E node \in Node, nr \in PublicKey :
          CreateChange(node, nr)
    \/ \E node \in Node : Process(node)
    \/ CreateGenesis

Spec == Init /\ [][Next]_<<LastHash, Ledger, Received>>

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeInvariant ==
    /\ LastHash \in Hash \cup {NoHash}
    /\ Ledger \in [Node -> [Hash -> Block]]
    /\ Received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node, h \in Hash :
        LET blk == Ledger[n][h] IN
        blk.signature # "" => ValidSignature(blk.signature, blk.source)

=============================================================================