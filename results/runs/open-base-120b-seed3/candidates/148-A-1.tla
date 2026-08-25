---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Hash,          \* Set of possible block hashes
    NoHash,        \* Sentinel value not in Hash
    NoHashVal,     \* Alias for NoHash (used in specifications)
    PrivateKey,    \* Set of private keys
    PublicKey,     \* Set of public keys
    Node,          \* Set of network nodes
    GenesisBalance,\* Total supply at genesis (a natural number)
    NoBlock,       \* Sentinel value for an empty block
    NoBlockVal,    \* Alias for NoBlock
    CalculateHash, \* Abstract hash operator (will be overridden by CalculateHashImpl)
    PrivToPub,     \* Mapping from PrivateKey to PublicKey
    NodePriv       \* Mapping from Node to its owned PrivateKey

\* ----------------------------------------------------------------------
\* Block definition
\* ----------------------------------------------------------------------
Block == [
    type          : {"genesis", "send", "open", "receive", "change"},
    prevHash      : Hash \cup {NoHash},
    account       : PublicKey,
    destination   : PublicKey \cup {NoHash},
    amount        : Nat,
    signature     : PrivateKey
]

\* The set of values that can appear in a ledger entry (either a real block or the sentinel)
BlockOrEmpty == Block \cup {NoBlockVal}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,    \* The hash of the most recently created block (or NoHash before genesis)
    ledger,      \* ledger[node][hash] = BlockOrEmpty
    received     \* received[node] = subset of Hash (blocks pending validation)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* A block is correctly signed if the public key derived from the signature
\* matches the account that owns the chain.
SignatureValid(b) ==
    LET pub == PrivToPub[b.signature] IN pub = b.account

\* The set of all hashes that exist in a node's ledger (i.e., are not NoBlockVal)
ExistingHashes(node) ==
    { h \in Hash : ledger[node][h] # NoBlockVal }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ ledger = [ n \in Node |-> [ h \in Hash |-> NoBlockVal ] ]
    /\ received = [ n \in Node |-> {} ]

\* ----------------------------------------------------------------------
\* Action: Create Genesis block (can occur only once)
\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHash                     \* Genesis not yet created
    \* Choose a node that will create the genesis block
    /\ \E n \in Node :
          LET pk == NodePriv[n] IN
          LET pub == PrivToPub[pk] IN
          LET blk ==
              [ type        |-> "genesis",
                prevHash    |-> NoHash,
                account     |-> pub,
                destination |-> NoHash,
                amount      |-> GenesisBalance,
                signature   |-> pk ]
          IN
          LET h == CalculateHash(blk, NoHash) IN
          /\ h \in Hash
          /\ \A m \in Node :
                ledger' = [ ledger EXCEPT ![m][h] = blk ]
          /\ lastHash' = h
          /\ UNCHANGED << received >>

\* ----------------------------------------------------------------------
\* Action: Create Send block
\* ----------------------------------------------------------------------
CreateSend ==
    /\ lastHash # NoHash                     \* Genesis must exist
    /\ \E n \in Node :
          LET pk == NodePriv[n] IN
          LET pub == PrivToPub[pk] IN
          \* Find the hash of the sender's latest block
          /\ \E prev \in ExistingHashes(n) :
                LET prevBlk == ledger[n][prev] IN
                /\ prevBlk.account = pub
                /\ prevBlk.type # "send" \* any type allowed as predecessor
                \* Determine the sender's current balance (simplified as GenesisBalance for example)
                \* In a full spec this would be a recursive function over the chain.
                LET bal == GenesisBalance \* placeholder
                /\ \E amt \in Nat :
                      amt <= bal
                      /\ \E destPub \in PublicKey :
                            LET blk ==
                                [ type        |-> "send",
                                  prevHash    |-> prev,
                                  account     |-> pub,
                                  destination |-> destPub,
                                  amount      |-> amt,
                                  signature   |-> pk ]
                            IN
                            LET h == CalculateHash(blk, prev) IN
                            /\ h \in Hash
                            /\ \A m \in Node :
                                  ledger' = [ ledger EXCEPT ![m][h] = blk ]
                            /\ lastHash' = h
                            /\ UNCHANGED << received >>

\* ----------------------------------------------------------------------
\* Action: Create Open block (opens a new account from a received send)
\* ----------------------------------------------------------------------
CreateOpen ==
    /\ \E n \in Node :
          LET pk == NodePriv[n] IN
          LET pub == PrivToPub[pk] IN
          \* Find a send block that targets this public key and is not yet opened
          /\ \E sendHash \in ExistingHashes(n) :
                LET sendBlk == ledger[n][sendHash] IN
                /\ sendBlk.type = "send"
                /\ sendBlk.destination = pub
                \* Ensure this account has no previous block
                /\ ~\E h \in ExistingHashes(n) :
                        LET b == ledger[n][h] IN b.account = pub /\ b.type # "open"
                LET blk ==
                    [ type        |-> "open",
                      prevHash    |-> NoHash,
                      account     |-> pub,
                      destination |-> NoHash,
                      amount      |-> sendBlk.amount,
                      signature   |-> pk ]
                IN
                LET h == CalculateHash(blk, NoHash) IN
                /\ h \in Hash
                /\ \A m \in Node :
                      ledger' = [ ledger EXCEPT ![m][h] = blk ]
                /\ lastHash' = h
                /\ UNCHANGED << received >>

\* ----------------------------------------------------------------------
\* Action: Create Receive block
\* ----------------------------------------------------------------------
CreateReceive ==
    /\ \E n \in Node :
          LET pk == NodePriv[n] IN
          LET pub == PrivToPub[pk] IN
          \* Find the latest block of this account
          /\ \E prev \in ExistingHashes(n) :
                LET prevBlk == ledger[n][prev] IN
                /\ prevBlk.account = pub
                \* Find a pending send block addressed to this account
                /\ \E sendHash \in ExistingHashes(n) :
                      LET sBlk == ledger[n][sendHash] IN
                      /\ sBlk.type = "send"
                      /\ sBlk.destination = pub
                      /\ ~\E h \in ExistingHashes(n) :
                            LET b == ledger[n][h] IN b.type = "receive" /\ b.prevHash = sendHash
                      LET blk ==
                          [ type        |-> "receive",
                            prevHash    |-> prev,
                            account     |-> pub,
                            destination |-> NoHash,
                            amount      |-> sBlk.amount,
                            signature   |-> pk ]
                      IN
                      LET h == CalculateHash(blk, prev) IN
                      /\ h \in Hash
                      /\ \A m \in Node :
                            ledger' = [ ledger EXCEPT ![m][h] = blk ]
                      /\ lastHash' = h
                      /\ UNCHANGED << received >>

\* ----------------------------------------------------------------------
\* Action: Create Change Representative block
\* ----------------------------------------------------------------------
CreateChange ==
    /\ \E n \in Node :
          LET pk == NodePriv[n] IN
          LET pub == PrivToPub[pk] IN
          /\ \E prev \in ExistingHashes(n) :
                LET prevBlk == ledger[n][prev] IN
                /\ prevBlk.account = pub
                LET blk ==
                    [ type        |-> "change",
                      prevHash    |-> prev,
                      account     |-> pub,
                      destination |-> NoHash,
                      amount      |-> 0,
                      signature   |-> pk ]
                IN
                LET h == CalculateHash(blk, prev) IN
                /\ h \in Hash
                /\ \A m \in Node :
                      ledger' = [ ledger EXCEPT ![m][h] = blk ]
                /\ lastHash' = h
                /\ UNCHANGED << received >>

\* ----------------------------------------------------------------------
\* Action: Process a received block (validation simplified)
\* ----------------------------------------------------------------------
ProcessReceived ==
    /\ \E n \in Node :
          /\ \E h \in received[n] :
                LET blk == ledger[n][h] IN
                /\ blk # NoBlockVal
                /\ SignatureValid(blk)
                /\ \A m \in Node :
                      ledger' = [ ledger EXCEPT ![m][h] = blk ]
                /\ received' = [ received EXCEPT ![n] = received[n] \ {h} ]
                /\ UNCHANGED lastHash

\* ----------------------------------------------------------------------
\* Next action (any of the defined actions)
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessReceived

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> BlockOrEmpty]]
    /\ received \in [Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* Safety invariant (cryptographic invariant)
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            LET b == ledger[n][h] IN
            b = NoBlockVal \/ SignatureValid(b)

\* ----------------------------------------------------------------------
\* Concrete implementation of CalculateHash (overridden by the .cfg)
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    (* A simple deterministic placeholder: hash is the pair (data.type, prev) encoded as a string *)
    LET repr == data.type \o "_" \o IF prev = NoHash THEN "0" ELSE ToString(prev) IN
    CHOOSE h \in Hash : TRUE

====