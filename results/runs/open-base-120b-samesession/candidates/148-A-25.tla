---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Hash,            \* Set of all possible block hashes
    NoHashVal,       \* Sentinel value meaning “no hash”
    NoHash,          \* Alias for NoHashVal (required by the cfg)
    PrivateKey,      \* Set of private keys
    PublicKey,       \* Set of public keys
    Node,            \* Set of network nodes
    GenesisBalance,  \* Total coins created by the genesis block (Nat)
    NoBlockVal,      \* Sentinel value meaning “no block”
    NoBlock,         \* Alias for NoBlockVal (required by the cfg)
    CalculateHash,   \* Abstract hash calculation operator
    PrivToPub        \* Mapping from a private key to its public key

\* ----------------------------------------------------------------------
\*  Operators that model the concrete hash function (overridden by the
\*  cfg with CalculateHashImpl)
\* ----------------------------------------------------------------------
CalculateHashImpl(d, p) == 
    (* For model checking we simply pick the next natural number as a hash.
       The concrete implementation can be substituted by the .cfg. *)
    IF p = NoHashVal THEN 1
    ELSE IF p + 1 \in Hash THEN p + 1
    ELSE CHOOSE h \in Hash : TRUE

\* ----------------------------------------------------------------------
\*  Block definition
\* ----------------------------------------------------------------------
Block == [
    type        : {"genesis", "send", "open", "receive", "change"},
    account     : PublicKey,
    amount      : Nat,
    prev        : Hash,
    dest        : PublicKey,   \* used by send blocks
    source      : Hash,        \* used by open/receive blocks
    signature   : PrivateKey
]

\* ----------------------------------------------------------------------
\*  State variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,        \* The most recent hash calculated (or NoHashVal)
    Blocks,          \* Global mapping from a hash to the corresponding block (or NoBlockVal)
    ledger,          \* Per‑node copy of the distributed ledger
    received         \* Per‑node set of hashes that are pending validation

\* ----------------------------------------------------------------------
\*  Helper definitions
\* ----------------------------------------------------------------------
\* The type of the ledger: for each node a map from Hash to Block∪{NoBlockVal}
LedgerType == [Node -> [Hash -> (Block \cup {NoBlockVal})]]

\* The type of the received set: for each node a subset of Hash
ReceivedType == [Node -> SUBSET Hash]

\* The type of the global block pool
BlocksType == [Hash -> (Block \cup {NoBlockVal})]

\* The tuple of all variables (used in the temporal formula)
vars == <<lastHash, Blocks, ledger, received>>

\* Validity of a signature: the private key must correspond to the block’s account
ValidSignature(b) == 
    /\ b.signature \in PrivateKey
    /\ PrivToPub[b.signature] = b.account

\* Type invariant – checks that each variable stays within its declared domain
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHashVal}
    /\ Blocks \in BlocksType
    /\ ledger \in LedgerType
    /\ received \in ReceivedType

\* Safety invariant – every stored block has a correct signature
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            /\ ledger[n][h] # NoBlockVal
            => ValidSignature(ledger[n][h])

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ Blocks = [h \in Hash |-> NoBlockVal]
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\*  Action: create the genesis block (only once)
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHashVal                     \* genesis not yet created
    /\ \A n \in Node : \A h \in Hash : ledger[n][h] = NoBlockVal
    /\ \E priv \in PrivateKey :
          LET pub == PrivToPub[priv] IN
          LET gBlock ==
                [ type      |-> "genesis",
                  account   |-> pub,
                  amount    |-> GenesisBalance,
                  prev      |-> NoHashVal,
                  dest      |-> NoBlockVal,
                  source    |-> NoBlockVal,
                  signature |-> priv ] IN
          LET h == CalculateHash(gBlock, NoHashVal) IN
          /\ h \in Hash
          /\ lastHash' = h
          /\ Blocks' = [Blocks EXCEPT ![h] = gBlock]
          /\ ledger' = [n \in Node |-> [h' \in Hash |-> IF h' = h THEN gBlock ELSE ledger[n][h']]]
          /\ received' = [n \in Node |-> received[n] ]      \* no pending hashes
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\*  Action: a node creates a send block
\* ----------------------------------------------------------------------
CreateSend ==
    \E n \in Node :
        \E priv \in PrivateKey :
            LET pub == PrivToPub[priv] IN
            /\ pub \in PublicKey
            /\ \E destPub \in PublicKey :
                \E amt \in Nat :
                    /\ amt <= GenesisBalance    \* (simplified balance check)
                    /\ \E prevHash \in Hash :
                        /\ ledger[n][prevHash] # NoBlockVal
                        /\ ledger[n][prevHash].account = pub
                        /\ LET sBlock ==
                            [ type      |-> "send",
                              account   |-> pub,
                              amount    |-> amt,
                              prev      |-> prevHash,
                              dest      |-> destPub,
                              source    |-> NoBlockVal,
                              signature |-> priv ] IN
                        LET h == CalculateHash(sBlock, prevHash) IN
                        /\ h \in Hash
                        /\ lastHash' = h
                        /\ Blocks' = [Blocks EXCEPT ![h] = sBlock]
                        /\ received' = [n' \in Node |-> received[n'] \cup {h}]
                        /\ UNCHANGED ledger
                        /\ UNCHANGED lastHash   \* lastHash already set above
\* ----------------------------------------------------------------------
\*  Action: a node creates an open block (opens a new account)
\* ----------------------------------------------------------------------
CreateOpen ==
    \E n \in Node :
        \E priv \in PrivateKey :
            LET pub == PrivToPub[priv] IN
            \E srcHash \in Hash :
                /\ Blocks[srcHash] # NoBlockVal
                /\ Blocks[srcHash].type = "send"
                /\ Blocks[srcHash].dest = pub
                /\ LET oBlock ==
                    [ type      |-> "open",
                      account   |-> pub,
                      amount    |-> Blocks[srcHash].amount,
                      prev      |-> NoHashVal,
                      dest      |-> NoBlockVal,
                      source    |-> srcHash,
                      signature |-> priv ] IN
                LET h == CalculateHash(oBlock, NoHashVal) IN
                /\ h \in Hash
                /\ lastHash' = h
                /\ Blocks' = [Blocks EXCEPT ![h] = oBlock]
                /\ received' = [n' \in Node |-> received[n'] \cup {h}]
                /\ UNCHANGED ledger

\* ----------------------------------------------------------------------
\*  Action: a node creates a receive block
\* ----------------------------------------------------------------------
CreateReceive ==
    \E n \in Node :
        \E priv \in PrivateKey :
            LET pub == PrivToPub[priv] IN
            \E srcHash \in Hash :
                /\ Blocks[srcHash] # NoBlockVal
                /\ Blocks[srcHash].type \in {"send","open"}
                /\ Blocks[srcHash].dest = pub \/ Blocks[srcHash].account = pub
                /\ \E prevHash \in Hash :
                    /\ ledger[n][prevHash] # NoBlockVal
                    /\ ledger[n][prevHash].account = pub
                    /\ LET rBlock ==
                        [ type      |-> "receive",
                          account   |-> pub,
                          amount    |-> Blocks[srcHash].amount,
                          prev      |-> prevHash,
                          dest      |-> NoBlockVal,
                          source    |-> srcHash,
                          signature |-> priv ] IN
                    LET h == CalculateHash(rBlock, prevHash) IN
                    /\ h \in Hash
                    /\ lastHash' = h
                    /\ Blocks' = [Blocks EXCEPT ![h] = rBlock]
                    /\ received' = [n' \in Node |-> received[n'] \cup {h}]
                    /\ UNCHANGED ledger

\* ----------------------------------------------------------------------
\*  Action: a node creates a change representative block
\* ----------------------------------------------------------------------
CreateChange ==
    \E n \in Node :
        \E priv \in PrivateKey :
            LET pub == PrivToPub[priv] IN
            \E newRep \in PublicKey :
                \E prevHash \in Hash :
                    /\ ledger[n][prevHash] # NoBlockVal
                    /\ ledger[n][prevHash].account = pub
                    /\ LET cBlock ==
                        [ type      |-> "change",
                          account   |-> pub,
                          amount    |-> 0,
                          prev      |-> prevHash,
                          dest      |-> newRep,
                          source    |-> NoBlockVal,
                          signature |-> priv ] IN
                    LET h == CalculateHash(cBlock, prevHash) IN
                    /\ h \in Hash
                    /\ lastHash' = h
                    /\ Blocks' = [Blocks EXCEPT ![h] = cBlock]
                    /\ received' = [n' \in Node |-> received[n'] \cup {h}]
                    /\ UNCHANGED ledger

\* ----------------------------------------------------------------------
\*  Action: a node processes a received block
\* ----------------------------------------------------------------------
ProcessReceived ==
    \E n \in Node :
        \E h \in received[n] :
            /\ Blocks[h] # NoBlockVal
            /\ ValidSignature(Blocks[h])
            /\ ledger' = [ledger EXCEPT ![n][h] = Blocks[h]]
            /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
            /\ UNCHANGED << lastHash, Blocks >>

\* ----------------------------------------------------------------------
\*  The overall next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessReceived

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\*  Invariants
\* ----------------------------------------------------------------------
\* (The .cfg will refer to these names)
\* TypeInvariant   – ensures variable types
\* SafetyInvariant – cryptographic signature correctness
====