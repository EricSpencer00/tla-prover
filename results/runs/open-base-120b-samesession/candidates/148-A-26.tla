---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Hash,                  \* Set of possible block hashes
  NoHashVal,             \* Sentinel value for "no hash"
  PrivateKey,            \* Set of private keys
  PublicKey,             \* Set of public keys
  Node,                  \* Set of network nodes
  GenesisBalance,        \* Total supply (a natural number)
  NoBlockVal,            \* Sentinel value for "no block"
  CalculateHash,         \* Abstract hash operator (overridden in the .cfg)
  NoHash,                \* Alias for NoHashVal
  NoBlock                \* Alias for NoBlockVal

\* ----------------------------------------------------------------------
\* Additional constants required for the model (they are not forced by the
\* .cfg but are useful for the specification)
CONSTANT
  PrivateToPublic,       \* Mapping from private keys to public keys
  GenesisPriv            \* Private key that owns the genesis account

\* ----------------------------------------------------------------------
\* Aliases for the sentinel values
NoHash == NoHashVal
NoBlock == NoBlockVal

\* ----------------------------------------------------------------------
\* Block record definition.  Only the fields relevant to the described
\* actions are included.
Block == [
  type    : {"genesis","send","open","receive","change"},
  prev    : Hash \/ {NoHash},
  acct    : PublicKey,
  amount  : Nat,
  dest    : PublicKey \/ {NoHash},
  source  : Hash \/ {NoHash},
  rep     : PublicKey \/ {NoHash},
  sig     : PrivateKey
]

\* ----------------------------------------------------------------------
\* Abstract hash implementation used for model checking.  The .cfg file
\* substitutes a concrete implementation for CalculateHash via
\* CalculateHashImpl.
CalculateHashImpl(b) ==
  CHOOSE h \in Hash : TRUE

\* The public identifier expected by the .cfg
CalculateHash(b) == CalculateHashImpl(b)

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
  lastHash,   \* The hash of the most recently created block (or NoHash)
  ledger,     \* Mapping from hashes to blocks (or NoBlock)
  received    \* Mapping from each node to the set of hashes it has received but not yet processed

\* ----------------------------------------------------------------------
\* Helper predicates
ValidSignature(b) ==
  /\ b.sig \in PrivateKey
  /\ PrivateToPublic[b.sig] = b.acct

BlockExists(h) == ledger[h] # NoBlock

\* ----------------------------------------------------------------------
\* Balance computation (recursive walk of an account chain)
Balance(acct) ==
  LET
    ChainHashes == { h \in Hash :
                       ledger[h] # NoBlock /\ ledger[h].acct = acct }
    MaxDepth == 0
    (* Helper that walks from a given hash backwards *)
    RecBal(h, acc) ==
      IF h = NoHash THEN acc
      ELSE
        LET blk == ledger[h] IN
        CASE blk.type = "send"   -> RecBal(blk.prev,
                                            acc - blk.amount)
        []   blk.type = "receive"-> RecBal(blk.prev,
                                            acc + ledger[blk.source].amount)
        []   blk.type = "open"   -> RecBal(blk.prev, acc)
        []   blk.type = "change" -> RecBal(blk.prev, acc)
        []   blk.type = "genesis"-> acc
        []   OTHER               -> acc
  IN
    IF ChainHashes = {} THEN 0
    ELSE
      (* The latest block of the account is the one that is not referenced
         as a `prev` of any other block belonging to the same account. *)
      LET latest ==
        CHOOSE h \in ChainHashes :
          \A h2 \in ChainHashes : ledger[h2].prev # h
      IN RecBal(latest, 0)

\* ----------------------------------------------------------------------
\* Initialization
Init ==
  /\ lastHash = NoHash
  /\ ledger = [h \in Hash |-> NoBlock]
  /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Action: creating the genesis block (once only)
CreateGenesis ==
  /\ lastHash = NoHash
  /\ \A n \in Node : received[n] = {}
  /\ let blk ==
        [ type    |-> "genesis",
          prev    |-> NoHash,
          acct    |-> PrivateToPublic[GenesisPriv],
          amount  |-> GenesisBalance,
          dest    |-> NoHash,
          source  |-> NoHash,
          rep     |-> NoHash,
          sig     |-> GenesisPriv ]
     in
        /\ h == CalculateHash(blk)
        /\ h \in Hash
        /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![h] = blk]
        /\ received' = [n \in Node |-> received[n] \cup {h}]
  /\ UNCHANGED << >>   \* no other variables

\* ----------------------------------------------------------------------
\* Action: a node creates a send block
CreateSend(node, dest, amt) ==
  /\ node \in Node
  /\ dest \in PublicKey
  /\ amt \in Nat
  /\ let acctPub == PrivateToPublic[NodeKey[node]] in
        Balance(acctPub) >= amt
  /\ \E prevHash \in Hash :
        ledger[prevHash] # NoBlock /\ ledger[prevHash].acct = acctPub
  /\ let blk ==
        [ type    |-> "send",
          prev    |-> prevHash,
          acct    |-> acctPub,
          amount  |-> amt,
          dest    |-> dest,
          source  |-> NoHash,
          rep     |-> NoHash,
          sig     |-> NodeKey[node] ]
     in
        /\ h == CalculateHash(blk)
        /\ h \in Hash
        /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![h] = blk]
        /\ received' = [n \in Node |-> received[n] \cup {h}]
  /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: a node creates an open block (first block of a new account)
CreateOpen(node, sendHash) ==
  /\ node \in Node
  /\ sendHash \in Hash
  /\ ledger[sendHash] # NoBlock
  /\ ledger[sendHash].type = "send"
  /\ ledger[sendHash].dest = PrivateToPublic[NodeKey[node]]
  /\ let blk ==
        [ type    |-> "open",
          prev    |-> NoHash,
          acct    |-> PrivateToPublic[NodeKey[node]],
          amount  |-> ledger[sendHash].amount,
          dest    |-> NoHash,
          source  |-> sendHash,
          rep     |-> NoHash,
          sig     |-> NodeKey[node] ]
     in
        /\ h == CalculateHash(blk)
        /\ h \in Hash
        /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![h] = blk]
        /\ received' = [n \in Node |-> received[n] \cup {h}]
  /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: a node creates a receive block
CreateReceive(node, sendHash) ==
  /\ node \in Node
  /\ sendHash \in Hash
  /\ ledger[sendHash] # NoBlock
  /\ ledger[sendHash].type = "send"
  /\ ledger[sendHash].dest = PrivateToPublic[NodeKey[node]]
  /\ \E prevHash \in Hash :
        ledger[prevHash] # NoBlock /\ ledger[prevHash].acct = PrivateToPublic[NodeKey[node]]
  /\ let blk ==
        [ type    |-> "receive",
          prev    |-> prevHash,
          acct    |-> PrivateToPublic[NodeKey[node]],
          amount  |-> 0,
          dest    |-> NoHash,
          source  |-> sendHash,
          rep     |-> NoHash,
          sig     |-> NodeKey[node] ]
     in
        /\ h == CalculateHash(blk)
        /\ h \in Hash
        /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![h] = blk]
        /\ received' = [n \in Node |-> received[n] \cup {h}]
  /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: a node creates a change-representative block
CreateChange(node, newRep) ==
  /\ node \in Node
  /\ newRep \in PublicKey
  /\ \E prevHash \in Hash :
        ledger[prevHash] # NoBlock /\ ledger[prevHash].acct = PrivateToPublic[NodeKey[node]]
  /\ let blk ==
        [ type    |-> "change",
          prev    |-> prevHash,
          acct    |-> PrivateToPublic[NodeKey[node]],
          amount  |-> 0,
          dest    |-> NoHash,
          source  |-> NoHash,
          rep     |-> newRep,
          sig     |-> NodeKey[node] ]
     in
        /\ h == CalculateHash(blk)
        /\ h \in Hash
        /\ lastHash' = h
        /\ ledger' = [ledger EXCEPT ![h] = blk]
        /\ received' = [n \in Node |-> received[n] \cup {h}]
  /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: a node processes a received block
Process(node, h) ==
  /\ node \in Node
  /\ h \in Hash
  /\ h \in received[node]
  /\ blk == ledger[h]
  /\ blk # NoBlock
  /\ ValidateBlock(blk, ledger)
  /\ received' = [received EXCEPT ![node] = @ \ {h}]
  /\ UNCHANGED << lastHash, ledger >>

\* ----------------------------------------------------------------------
\* Validation predicate for a block (signature and reference checks)
ValidateBlock(b, l) ==
  /\ ValidSignature(b)
  /\ CASE b.type = "genesis" -> TRUE
     [] b.type = "send"   -> b.prev # NoHash /\ l[b.prev] # NoBlock
     [] b.type = "open"   -> b.source # NoHash /\ l[b.source] # NoBlock
     [] b.type = "receive"-> b.prev # NoHash /\ l[b.prev] # NoBlock
                            /\ b.source # NoHash /\ l[b.source] # NoBlock
     [] b.type = "change" -> b.prev # NoHash /\ l[b.prev] # NoBlock
     [] OTHER             -> FALSE

\* ----------------------------------------------------------------------
\* The next-state relation combines all possible actions
Next ==
  \/ CreateGenesis
  \/ \E n \in Node, d \in PublicKey, a \in Nat : CreateSend(n, d, a)
  \/ \E n \in Node, sh \in Hash : CreateOpen(n, sh)
  \/ \E n \in Node, sh \in Hash : CreateReceive(n, sh)
  \/ \E n \in Node, r \in PublicKey : CreateChange(n, r)
  \/ \E n \in Node, h \in Hash : Process(n, h)

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* Type invariant
TypeInvariant ==
  /\ lastHash \in Hash \/ {NoHash}
  /\ ledger \in [Hash -> (Block \/ {NoBlock})]
  /\ received \in [Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* Safety invariant (all stored blocks have a valid signature)
SafetyInvariant ==
  \A h \in Hash :
    IF ledger[h] # NoBlock THEN ValidSignature(ledger[h]) ELSE TRUE

\* ----------------------------------------------------------------------
\* Mapping from nodes to the private key they own (used in actions)
NodeKey == [n \in Node |-> CHOOSE pk \in PrivateKey : TRUE]

====