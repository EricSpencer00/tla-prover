---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(*  CONSTANTS (to be supplied by the .cfg file)                           *)
(***************************************************************************)
CONSTANTS
    Hash,                \* Set of all possible block hashes
    NoHashVal,           \* Sentinel value meaning “no hash yet”
    PrivateKey,          \* Set of private keys
    PublicKey,           \* Set of public keys
    Node,                \* Set of network nodes
    GenesisBalance,      \* Total supply placed in the genesis block
    NoBlockVal,          \* Sentinel meaning “no block stored”
    CalculateHash,       \* Abstract hash operator (will be overridden)
    NoHash,              \* Alternative sentinel for a hash (unused here)
    NoBlock,             \* Alternative sentinel for a block (unused here)
    Priv2Pub,            \* Mapping from private to public keys
    NodeOwnedKeys        \* Mapping from node to the set of private keys it controls

(***************************************************************************)
(*  Assumptions constraining the additional constants                     *)
(***************************************************************************)
ASSUME Priv2Pub \in [PrivateKey -> PublicKey]
ASSUME NodeOwnedKeys \in [Node -> SUBSET PrivateKey]

(***************************************************************************)
(*  Block record definition                                               *)
(***************************************************************************)
Block ==
    [ type        : {"Genesis", "Send", "Open", "Receive", "Change"},
      owner       : PublicKey,                \* account that owns the chain
      prev        : Hash \cup {NoHashVal},    \* previous block hash in the chain
      amount      : Nat,                      \* amount transferred (if applicable)
      recipient   : PublicKey \cup {NoHashVal}, \* destination account (send)
      source      : Hash \cup {NoHashVal},    \* referenced send block (open/receive)
      rep         : PublicKey \cup {NoHashVal}, \* representative (change)
      sigOwner    : PrivateKey,               \* private key that signed the block
      sigHash     : Hash                      \* hash that was signed
    ]

(***************************************************************************)
(*  Helper definitions                                                    *)
(***************************************************************************)

\* The hash of a block is defined by the abstract hash operator.
BlockHash(b) == CalculateHash(b, b.prev)

\* A block is present (i.e., not the empty sentinel)
IsBlock(b) == b # NoBlockVal

\* Signature validation: the block must be signed by the private key that
\* corresponds to the public key owning the chain, and the signed hash
\* must equal the block's computed hash.
SigValid(b) ==
    /\ Priv2Pub[b.sigOwner] = b.owner
    /\ b.sigHash = BlockHash(b)

\* Existence of a block with a given hash in a node's ledger
BlockExists(node, h) ==
    LET blk == Ledger[node][h] IN IsBlock(blk)

\* Retrieve the latest block hash for a given account on a node.
\* (If the account has no blocks yet, return NoHashVal.)
LatestHash(node, acct) ==
    CASE
        \E h \in Hash :
            /\ Ledger[node][h].owner = acct
            /\ \A h2 \in Hash :
                (Ledger[node][h2].owner = acct) => (h2 = h) \/ (Ledger[node][h2].prev # h)
        => NoHashVal

(***************************************************************************)
(*  State variables                                                       *)
(***************************************************************************)
VARIABLES
    LastHash,    \* The hash of the most recently created block (global)
    Ledger,      \* Mapping: node -> (hash -> Block or NoBlockVal)
    Received     \* Mapping: node -> SUBSET of Hash (blocks received but not yet processed)

(***************************************************************************)
(*  Initial state                                                         *)
(***************************************************************************)
Init ==
    /\ LastHash = NoHashVal
    /\ Ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ Received = [n \in Node |-> {}]

(***************************************************************************)
(*  Action: Create the genesis block                                      *)
(***************************************************************************)
CreateGenesis ==
    /\ LastHash = NoHashVal
    \* Choose a node and a private key belonging to that node
    /\ \E n \in Node, pk \in PrivateKey :
        /\ pk \in NodeOwnedKeys[n]
        /\ LET blk == [ type       |-> "Genesis",
                        owner      |-> Priv2Pub[pk],
                        prev       |-> NoHashVal,
                        amount     |-> GenesisBalance,
                        recipient  |-> NoHashVal,
                        source     |-> NoHashVal,
                        rep        |-> NoHashVal,
                        sigOwner   |-> pk,
                        sigHash    |-> CalculateHashImpl(
                                        [type |-> "Genesis",
                                         owner |-> Priv2Pub[pk],
                                         prev |-> NoHashVal,
                                         amount |-> GenesisBalance,
                                         recipient |-> NoHashVal,
                                         source |-> NoHashVal,
                                         rep |-> NoHashVal],
                                        NoHashVal) ]
        IN
        LET h == BlockHash(blk) IN
            /\ h \in Hash
            /\ LastHash' = h
            /\ Ledger' = [n2 \in Node |-> Ledger[n2] \oplus [h |-> blk]]
            /\ Received' = Received
            /\ UNCHANGED << >>

(***************************************************************************)
(*  Action: Create a send block                                            *)
(***************************************************************************)
CreateSend ==
    /\ LastHash # NoHashVal
    /\ \E n \in Node, pk \in PrivateKey, amt \in Nat, rec \in PublicKey :
        /\ pk \in NodeOwnedKeys[n]
        /\ LET acct == Priv2Pub[pk] IN
           /\ amt <= Balance(node=n, acct=acct)          \* Balance defined later
        /\ LET prevHash == LatestHash(n, acct) IN
           prevHash # NoHashVal
        /\ LET blk == [ type       |-> "Send",
                        owner      |-> acct,
                        prev       |-> prevHash,
                        amount     |-> amt,
                        recipient  |-> rec,
                        source     |-> NoHashVal,
                        rep        |-> NoHashVal,
                        sigOwner   |-> pk,
                        sigHash    |-> CalculateHashImpl(
                                        [type |-> "Send",
                                         owner |-> acct,
                                         prev |-> prevHash,
                                         amount |-> amt,
                                         recipient |-> rec,
                                         source |-> NoHashVal,
                                         rep |-> NoHashVal],
                                        prevHash) ]
        IN
        LET h == BlockHash(blk) IN
            /\ h \in Hash
            /\ LastHash' = h
            /\ Ledger' = [n2 \in Node |-> Ledger[n2] \oplus [h |-> blk]]
            /\ Received' = [n2 \in Node |-> Received[n2] \cup {h}]
            /\ UNCHANGED << >>

(***************************************************************************)
(*  Action: Create an open block (first block of a new account)           *)
(***************************************************************************)
CreateOpen ==
    /\ LastHash # NoHashVal
    /\ \E n \in Node, pk \in PrivateKey, srcHash \in Hash :
        /\ pk \in NodeOwnedKeys[n]
        /\ LET acct == Priv2Pub[pk] IN
           /\ \A h \in Hash : Ledger[n][h].owner # acct      \* account not yet opened
        /\ BlockExists(n, srcHash)
        /\ LET srcBlk == Ledger[n][srcHash] IN
           /\ srcBlk.type = "Send"
           /\ srcBlk.recipient = acct
        /\ LET blk == [ type       |-> "Open",
                        owner      |-> acct,
                        prev       |-> NoHashVal,
                        amount     |-> srcBlk.amount,
                        recipient  |-> NoHashVal,
                        source     |-> srcHash,
                        rep        |-> NoHashVal,
                        sigOwner   |-> pk,
                        sigHash    |-> CalculateHashImpl(
                                        [type |-> "Open",
                                         owner |-> acct,
                                         prev |-> NoHashVal,
                                         amount |-> srcBlk.amount,
                                         source |-> srcHash,
                                         rep |-> NoHashVal],
                                        NoHashVal) ]
        IN
        LET h == BlockHash(blk) IN
            /\ h \in Hash
            /\ LastHash' = h
            /\ Ledger' = [n2 \in Node |-> Ledger[n2] \oplus [h |-> blk]]
            /\ Received' = [n2 \in Node |-> Received[n2] \cup {h}]
            /\ UNCHANGED << >>

(***************************************************************************)
(*  Action: Create a receive block                                         *)
(***************************************************************************)
CreateReceive ==
    /\ LastHash # NoHashVal
    /\ \E n \in Node, pk \in PrivateKey, srcHash \in Hash :
        /\ pk \in NodeOwnedKeys[n]
        /\ LET acct == Priv2Pub[pk] IN
           /\ BlockExists(n, srcHash)
        /\ LET srcBlk == Ledger[n][srcHash] IN
           /\ srcBlk.type = "Send"
           /\ srcBlk.recipient = acct
        /\ LET prevHash == LatestHash(n, acct) IN
           prevHash # NoHashVal
        /\ LET blk == [ type       |-> "Receive",
                        owner      |-> acct,
                        prev       |-> prevHash,
                        amount     |-> srcBlk.amount,
                        recipient  |-> NoHashVal,
                        source     |-> srcHash,
                        rep        |-> NoHashVal,
                        sigOwner   |-> pk,
                        sigHash    |-> CalculateHashImpl(
                                        [type |-> "Receive",
                                         owner |-> acct,
                                         prev |-> prevHash,
                                         amount |-> srcBlk.amount,
                                         source |-> srcHash],
                                        prevHash) ]
        IN
        LET h == BlockHash(blk) IN
            /\ h \in Hash
            /\ LastHash' = h
            /\ Ledger' = [n2 \in Node |-> Ledger[n2] \oplus [h |-> blk]]
            /\ Received' = [n2 \in Node |-> Received[n2] \cup {h}]
            /\ UNCHANGED << >>

(***************************************************************************)
(*  Action: Create a change-representative block                           *)
(***************************************************************************)
CreateChange ==
    /\ LastHash # NoHashVal
    /\ \E n \in Node, pk \in PrivateKey, newRep \in PublicKey :
        /\ pk \in NodeOwnedKeys[n]
        /\ LET acct == Priv2Pub[pk] IN
           LET prevHash == LatestHash(n, acct) IN
               prevHash # NoHashVal
        /\ LET blk == [ type       |-> "Change",
                        owner      |-> acct,
                        prev       |-> prevHash,
                        amount     |-> 0,
                        recipient  |-> NoHashVal,
                        source     |-> NoHashVal,
                        rep        |-> newRep,
                        sigOwner   |-> pk,
                        sigHash    |-> CalculateHashImpl(
                                        [type |-> "Change",
                                         owner |-> acct,
                                         prev |-> prevHash,
                                         rep |-> newRep],
                                        prevHash) ]
        IN
        LET h == BlockHash(blk) IN
            /\ h \in Hash
            /\ LastHash' = h
            /\ Ledger' = [n2 \in Node |-> Ledger[n2] \oplus [h |-> blk]]
            /\ Received' = [n2 \in Node |-> Received[n2] \cup {h}]
            /\ UNCHANGED << >>

(***************************************************************************)
(*  Action: Process a received block (validation & insertion)            *)
(***************************************************************************)
ProcessReceived ==
    /\ \E n \in Node, h \in Received[n] :
        LET blk == Ledger[n][h] IN
        /\ IsBlock(blk)
        /\ SigValid(blk)                \* cryptographic check
        /\ \* Basic reference checks (simplified)
           (blk.type = "Send"  => blk.prev # NoHashVal)
        /\ \* Additional type‑specific validation can be added here
        /\ Ledger' = Ledger                 \* ledger already contains the block
        /\ Received' = [n2 \in Node |-> IF n2 = n THEN Received[n2] \ {h} ELSE Received[n2]]
        /\ UNCHANGED << LastHash >>

(***************************************************************************)
(*  Next-state relation                                                    *)
(***************************************************************************)
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessReceived

(***************************************************************************)
(*  Safety property: Type invariant                                       *)
(***************************************************************************)
TypeInvariant ==
    /\ LastHash \in Hash \cup {NoHashVal}
    /\ Ledger \in [Node -> [Hash -> (Block \cup {NoBlockVal})]]
    /\ Received \in [Node -> SUBSET Hash]

(***************************************************************************)
(*  Safety property: Cryptographic invariant                              *)
(***************************************************************************)
SafetyInvariant ==
    \A n \in Node, h \in Hash :
        LET blk == Ledger[n][h] IN
        (blk # NoBlockVal) => SigValid(blk)

(***************************************************************************)
(*  Specification                                                          *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<LastHash, Ledger, Received>>

(***************************************************************************)
(*  Helper definitions required by actions                              *)
(***************************************************************************)

\* Compute the balance of an account on a given node by walking its chain.
Balance(node, acct) ==
    LET hashes == { h \in Hash : Ledger[node][h].owner = acct } IN
    LET ordered ==
        IF hashes = {} THEN {}
        ELSE
            LET start == { h \in hashes : Ledger[node][h].prev = NoHashVal } IN
            IF start = {} THEN {}
            ELSE
                [ seq \in Seq(Hash) |
                    /\ Len(seq) = Cardinality(hashes)
                    /\ seq[1] \in start
                    /\ \A i \in 1..Len(seq)-1 :
                        LET cur == seq[i] IN
                        \E nxt \in hashes :
                            Ledger[node][nxt].prev = cur
                ]
    IN
    IF ordered = {} THEN 0
    ELSE
        LET lastHash == Head(ordered) IN
        LET lastBlk == Ledger[node][lastHash] IN
        CASE
            lastBlk.type = "Genesis" => lastBlk.amount
            lastBlk.type = "Send"    => Balance(node, acct) - lastBlk.amount
            lastBlk.type = "Open"    => lastBlk.amount
            lastBlk.type = "Receive" => Balance(node, acct) + lastBlk.amount
            lastBlk.type = "Change"  => Balance(node, acct)
            OTHER                    => 0

(***************************************************************************)
(*  Operator required by the configuration: a concrete hash implementation*)
(***************************************************************************)
CalculateHashImpl(blockData, prevHash) ==
    (* In a concrete model this would be a bounded hash function.
       Here we simply return an arbitrary element of Hash. *)
    CHOOSE h \in Hash : TRUE

=============================================================================