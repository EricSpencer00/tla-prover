---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Hash,          \* The set of all possible block hashes
    NoHashVal,     \* Sentinel value meaning “no hash yet”
    PrivateKey,    \* Set of private keys
    PublicKey,     \* Set of public keys
    Node,          \* Set of network nodes
    GenesisBalance,\* Total supply of coins at genesis (a natural number)
    NoBlockVal,    \* Sentinel value meaning “no block stored”
    CalculateHash, \* Abstract hash‑calculation operator
    NoHash,        \* Another sentinel for “no hash” used inside blocks
    NoBlock        \* Another sentinel for “no block” used inside blocks

\* ----------------------------------------------------------------------
\*  Types
\* ----------------------------------------------------------------------
Block ==
    [ type        : {"genesis","send","open","receive","change"},
      prev        : Hash \/ {NoHash},
      account     : PublicKey,
      sig         : STRING,                \* placeholder for a signature
      amount      : Nat,
      dest        : PublicKey,            \* used by send/open blocks
      source      : Hash \/ {NoHash},      \* used by receive blocks
      repr        : PublicKey ]            \* voting representative

\* ----------------------------------------------------------------------
\*  State variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,   \* The hash of the most recently created block (or NoHashVal)
    ledger,     \* [node \in Node -> [hash \in Hash -> Block \/ {NoBlockVal}]]
    received    \* [node \in Node -> SUBSET Hash]   \* blocks that have arrived but not yet processed

\* ----------------------------------------------------------------------
\*  Helper operators
\* ----------------------------------------------------------------------
\* Mapping from a private key to its public key – modelled as an arbitrary
\* total function (the concrete mapping will be supplied by the .cfg if desired).
PrivToPub \in [PrivateKey -> PublicKey]

\* A very simple placeholder signature function.  In a real model this would
\* be replaced by a cryptographic primitive; for model checking we merely
\* require that the signature string be deterministic with respect to the
\* private key and the block data.
Sign(sk, data) == "sig_" \o ToString(sk) \o "_" \o ToString(data)

\* Predicate that a block’s signature matches the public key of the account
\* that owns the chain.
SigValid(b) ==
    LET pk == b.account IN
    b.sig = Sign( CHOOSE sk \in PrivateKey : PrivToPub[sk] = pk,
                 SerializeBlock(b) )

\* Serialize a block to a string – only needed for the dummy Sign definition.
SerializeBlock(b) ==
    << b.type, b.prev, b.account, b.amount, b.dest, b.source, b.repr >>

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ ledger   = [ n \in Node |-> [ h \in Hash |-> NoBlockVal ] ]
    /\ received = [ n \in Node |-> {} ]

\* ----------------------------------------------------------------------
\*  Actions
\* ----------------------------------------------------------------------
\*  (1) Create the genesis block.  Can occur only when no block has yet been
\*      created.  The block is instantly added to every node’s ledger and
\*      broadcast (the broadcast set stays empty because the block is already
\*      present everywhere).
CreateGenesis ==
    /\ lastHash = NoHashVal
    /\ \E sk \in PrivateKey :
          LET pk == PrivToPub[sk] IN
          LET b  ==
              [ type    |-> "genesis",
                prev    |-> NoHash,
                account |-> pk,
                sig     |-> Sign(sk, "genesis"),
                amount  |-> GenesisBalance,
                dest    |-> pk,
                source  |-> NoHash,
                repr    |-> pk ] IN
          LET h  == CalculateHash(b, NoHashVal) IN
          /\ lastHash' = h
          /\ ledger'   = [ n \in Node |-> [ h2 \in Hash |-> IF h2 = h THEN b ELSE ledger[n][h2] ] ]
          /\ received' = [ n \in Node |-> {} ]
    /\ UNCHANGED << >>

\*  (2) Create a send block.  The creator is some node that owns a private key.
CreateSend ==
    /\ lastHash # NoHashVal               \* genesis must already exist
    /\ \E n \in Node, sk \in PrivateKey :
         LET pk == PrivToPub[sk] IN
         /\ pk \in PublicKey               \* sanity
         /\ \E hPrev \in Hash :
                /\ ledger[n][hPrev] # NoBlockVal
                /\ ledger[n][hPrev].account = pk
                /\ LET bal == Balance(pk, n) IN
                   \E amt \in Nat :
                       /\ amt <= bal
                       /\ \E destPk \in PublicKey :
                            LET b ==
                                [ type    |-> "send",
                                  prev    |-> hPrev,
                                  account |-> pk,
                                  sig     |-> Sign(sk, <<hPrev, amt, destPk>>),
                                  amount  |-> amt,
                                  dest    |-> destPk,
                                  source  |-> NoHash,
                                  repr    |-> ledger[n][hPrev].repr ] IN
                            LET h == CalculateHash(b, hPrev) IN
                            /\ lastHash' = h
                            /\ ledger'   = [ n2 \in Node |-> [ h2 \in Hash |-> IF h2 = h THEN b ELSE ledger[n2][h2] ] ]
                            /\ received' = [ n2 \in Node |-> received[n2] \cup { h } ]
         /\ UNCHANGED << >>

\*  (3) Create an open block – a node opens a new account by referencing a
\*      send block that was addressed to its public key.
CreateOpen ==
    /\ \E n \in Node, sk \in PrivateKey, sendHash \in Hash :
         LET pk == PrivToPub[sk] IN
         LET sendBlk == ledger[n][sendHash] IN
         /\ sendBlk # NoBlockVal
         /\ sendBlk.type = "send"
         /\ sendBlk.dest = pk
         /\ LET b ==
                [ type    |-> "open",
                  prev    |-> NoHash,
                  account |-> pk,
                  sig     |-> Sign(sk, <<sendHash>>),
                  amount  |-> sendBlk.amount,
                  dest    |-> pk,
                  source  |-> sendHash,
                  repr    |-> sendBlk.repr ] IN
         LET h == CalculateHash(b, NoHash) IN
         /\ lastHash' = h
         /\ ledger'   = [ n2 \in Node |-> [ h2 \in Hash |-> IF h2 = h THEN b ELSE ledger[n2][h2] ] ]
         /\ received' = [ n2 \in Node |-> received[n2] \cup { h } ]
    /\ UNCHANGED << >>

\*  (4) Create a receive block – a node claims a pending send.
CreateReceive ==
    /\ \E n \in Node, sk \in PrivateKey, recvPrev \in Hash, sendHash \in Hash :
         LET pk == PrivToPub[sk] IN
         LET prevBlk == ledger[n][recvPrev] IN
         LET sendBlk == ledger[n][sendHash] IN
         /\ prevBlk # NoBlockVal
         /\ prevBlk.account = pk
         /\ sendBlk # NoBlockVal
         /\ sendBlk.type = "send"
         /\ sendBlk.dest = pk
         /\ LET b ==
                [ type    |-> "receive",
                  prev    |-> recvPrev,
                  account |-> pk,
                  sig     |-> Sign(sk, <<recvPrev, sendHash>>),
                  amount  |-> sendBlk.amount,
                  dest    |-> pk,
                  source  |-> sendHash,
                  repr    |-> prevBlk.repr ] IN
         LET h == CalculateHash(b, recvPrev) IN
         /\ lastHash' = h
         /\ ledger'   = [ n2 \in Node |-> [ h2 \in Hash |-> IF h2 = h THEN b ELSE ledger[n2][h2] ] ]
         /\ received' = [ n2 \in Node |-> received[n2] \cup { h } ]
    /\ UNCHANGED << >>

\*  (5) Change representative block.
CreateChange ==
    /\ \E n \in Node, sk \in PrivateKey, prevHash \in Hash :
         LET pk == PrivToPub[sk] IN
         LET prevBlk == ledger[n][prevHash] IN
         /\ prevBlk # NoBlockVal
         /\ prevBlk.account = pk
         /\ \E newRepr \in PublicKey :
                LET b ==
                    [ type    |-> "change",
                      prev    |-> prevHash,
                      account |-> pk,
                      sig     |-> Sign(sk, <<prevHash, newRepr>>),
                      amount  |-> 0,
                      dest    |-> pk,
                      source  |-> NoHash,
                      repr    |-> newRepr ] IN
                LET h == CalculateHash(b, prevHash) IN
                /\ lastHash' = h
                /\ ledger'   = [ n2 \in Node |-> [ h2 \in Hash |-> IF h2 = h THEN b ELSE ledger[n2][h2] ] ]
                /\ received' = [ n2 \in Node |-> received[n2] \cup { h } ]
    /\ UNCHANGED << >>

\*  (6) Process a received block on a particular node – validation is
\*      simplified: we only check that the block exists in the received set
\*      and that its signature is valid.
ProcessBlock ==
    /\ \E n \in Node, h \in Hash :
         /\ h \in received[n]
         /\ LET b == ledger[n][h] IN
            /\ b # NoBlockVal
            /\ SigValid(b)
         /\ received' = [ n2 \in Node |-> IF n2 = n THEN received[n2] \ REMOVE { h } ELSE received[n2] ]
    /\ UNCHANGED << lastHash, ledger >>

\*  The overall Next relation is the disjunction of all possible actions.
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\* ----------------------------------------------------------------------
\*  Derived definitions
\* ----------------------------------------------------------------------
\* Recursive balance calculation: walk the chain of blocks belonging to an
\* account on a given node and sum the net received amounts.
Balance(pk, n) ==
    LET chainHashes == { h \in Hash : ledger[n][h] # NoBlockVal /\ ledger[n][h].account = pk } IN
    LET amounts == { b.amount : b \in { ledger[n][h] : h \in chainHashes } } IN
    IF chainHashes = {} THEN 0 ELSE Sum(SeqFromSet(amounts))

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<< lastHash, ledger, received >>

\* ----------------------------------------------------------------------
\*  Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash \/ lastHash = NoHashVal
    /\ ledger \in [Node -> [Hash -> (Block \/ {NoBlockVal})]]
    /\ received \in [Node -> SUBSET Hash]

SafetyInvariant ==
    \A n \in Node :
        \A h \in Hash :
            IF ledger[n][h] # NoBlockVal
            THEN SigValid(ledger[n][h])
            ELSE TRUE

\* ----------------------------------------------------------------------
\*  Operator required by the .cfg to supply a concrete hash implementation.
\* ----------------------------------------------------------------------
CalculateHashImpl(data, prev) ==
    \* The concrete model will replace CalculateHashImpl with a finite version.
    CalculateHash(data, prev)

====