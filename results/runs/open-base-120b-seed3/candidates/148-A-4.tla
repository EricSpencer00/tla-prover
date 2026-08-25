---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Hash,          \* Set of all possible block hashes
    NoHashVal,     \* A distinguished hash value representing “no hash”
    PrivateKey,    \* Set of private keys
    PublicKey,     \* Set of public keys
    Node,          \* Set of network nodes
    GenesisBalance,\* Total number of coins at genesis
    NoBlockVal,    \* Sentinel value meaning “no block stored”
    CalculateHash, \* Abstract hash operator (overridden by CalculateHashImpl)
    NoHash,        \* Sentinel hash used for the initial state
    NoBlock        \* Sentinel block value (may be the same as NoBlockVal)

\* ----------------------------------------------------------------------
\* Record type for a block.  Fields not used by a particular block type
\* may contain arbitrary values (here we use the sentinel constants).
Block ==
    [ type          : {"Genesis", "Send", "Open", "Receive", "Change"},
      prev          : Hash,
      account       : PublicKey,
      amount        : Nat,
      recipient     : PublicKey,
      source        : Hash,
      representative: PublicKey,
      signer        : PrivateKey ]

\* ----------------------------------------------------------------------
\* Mapping from private keys to their public counterparts.  This is left
\* abstract; the model checker may instantiate it via a constant.
PrivateToPublic \in [PrivateKey -> PublicKey]

\* ----------------------------------------------------------------------
\* Helper that extracts the data that is fed to the hash function.
BlockData(b) ==
    [type |-> b.type,
     account |-> b.account,
     amount |-> b.amount,
     recipient |-> b.recipient,
     source |-> b.source,
     representative |-> b.representative]

\* ----------------------------------------------------------------------
\* Abstract hash operator; the concrete implementation is supplied by
\* the configuration file as CalculateHashImpl.
CalculateHash(data, prev) == CalculateHashImpl(data, prev)

\* ----------------------------------------------------------------------
\* Signature validation: a block is valid iff the public key derived
\* from the signer matches the block’s account field.
ValidSignature(b) ==
    PrivateToPublic[b.signer] = b.account

\* ----------------------------------------------------------------------
\* Predicate that checks whether a stored block satisfies all
\* protocol‑specific validation rules.
ValidBlock(h) ==
    LET b == ledger[h] IN
    /\ b # NoBlockVal
    /\ ValidSignature(b)
    /\ CASE b.type = "Genesis"   -> /\ b.prev = NoHash
                                    /\ b.amount = GenesisBalance
         [] b.type = "Send"      -> /\ b.prev # NoHash
                                    /\ b.prev \in Hash
                                    /\ ledger[b.prev] # NoBlockVal
                                    /\ b.amount <= GenesisBalance      \* abstract overdraft check
         [] b.type = "Open"      -> /\ b.prev = NoHash
                                    /\ b.source \in Hash
                                    /\ ledger[b.source].type = "Send"
                                    /\ ledger[b.source].recipient = b.account
         [] b.type = "Receive"   -> /\ b.prev \in Hash
                                    /\ ledger[b.prev] # NoBlockVal
                                    /\ b.source \in Hash
                                    /\ ledger[b.source].type = "Send"
                                    /\ ledger[b.source].recipient = b.account
         [] b.type = "Change"    -> /\ b.prev \in Hash
                                    /\ ledger[b.prev] # NoBlockVal
         [] OTHER               -> FALSE

\* ----------------------------------------------------------------------
VARIABLES
    lastHash,   \* The hash of the most recently created block (or NoHash)
    ledger,     \* Mapping from Hash to Block (or NoBlockVal)
    received    \* Mapping Node -> SUBSET Hash of blocks pending validation

vars == <<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHash
    /\ ledger = [h \in Hash |-> NoBlockVal]
    /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
CreateGenesis ==
    /\ lastHash = NoHash
    /\ \E n \in Node, priv \in PrivateKey :
          LET acc == PrivateToPublic[priv] IN
          LET blk ==
              [ type          |-> "Genesis",
                prev          |-> NoHash,
                account       |-> acc,
                amount        |-> GenesisBalance,
                recipient     |-> NoHashVal,
                source        |-> NoHashVal,
                representative|-> NoHashVal,
                signer        |-> priv ] IN
          /\ \E h \in Hash \ {NoHash} :
                /\ ledger' = [ledger EXCEPT ![h] = blk]
                /\ lastHash' = h
                /\ received' = [node \in Node |-> received[node] \cup {h}]
                /\ UNCHANGED << >>   \* no other variables
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
CreateSend ==
    /\ \E n \in Node, priv \in PrivateKey, amt \in Nat, rcpt \in PublicKey :
          LET acc == PrivateToPublic[priv] IN
          /\ \E prevHash \in Hash :
                /\ ledger[prevHash].account = acc
                /\ ledger[prevHash] # NoBlockVal
                LET blk ==
                    [ type          |-> "Send",
                      prev          |-> prevHash,
                      account       |-> acc,
                      amount        |-> amt,
                      recipient     |-> rcpt,
                      source        |-> NoHashVal,
                      representative|-> NoHashVal,
                      signer        |-> priv ] IN
                /\ \E h \in Hash \ {NoHash} :
                      /\ ledger' = [ledger EXCEPT ![h] = blk]
                      /\ received' = [node \in Node |-> received[node] \cup {h}]
                      /\ UNCHANGED lastHash
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
CreateOpen ==
    /\ \E n \in Node, priv \in PrivateKey, srcHash \in Hash :
          LET acc == PrivateToPublic[priv] IN
          /\ ledger[srcHash].type = "Send"
          /\ ledger[srcHash].recipient = acc
          LET amt == ledger[srcHash].amount IN
          LET blk ==
              [ type          |-> "Open",
                prev          |-> NoHash,
                account       |-> acc,
                amount        |-> amt,
                recipient     |-> NoHashVal,
                source        |-> srcHash,
                representative|-> NoHashVal,
                signer        |-> priv ] IN
          /\ \E h \in Hash \ {NoHash} :
                /\ ledger' = [ledger EXCEPT ![h] = blk]
                /\ received' = [node \in Node |-> received[node] \cup {h}]
                /\ UNCHANGED lastHash
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
CreateReceive ==
    /\ \E n \in Node, priv \in PrivateKey, prevHash \in Hash, srcHash \in Hash :
          LET acc == PrivateToPublic[priv] IN
          /\ ledger[prevHash].account = acc
          /\ ledger[srcHash].type = "Send"
          /\ ledger[srcHash].recipient = acc
          LET amt == ledger[srcHash].amount IN
          LET blk ==
              [ type          |-> "Receive",
                prev          |-> prevHash,
                account       |-> acc,
                amount        |-> amt,
                recipient     |-> NoHashVal,
                source        |-> srcHash,
                representative|-> NoHashVal,
                signer        |-> priv ] IN
          /\ \E h \in Hash \ {NoHash} :
                /\ ledger' = [ledger EXCEPT ![h] = blk]
                /\ received' = [node \in Node |-> received[node] \cup {h}]
                /\ UNCHANGED lastHash
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
CreateChange ==
    /\ \E n \in Node, priv \in PrivateKey, prevHash \in Hash, rep \in PublicKey :
          LET acc == PrivateToPublic[priv] IN
          /\ ledger[prevHash].account = acc
          LET blk ==
              [ type          |-> "Change",
                prev          |-> prevHash,
                account       |-> acc,
                amount        |-> 0,
                recipient     |-> NoHashVal,
                source        |-> NoHashVal,
                representative|-> rep,
                signer        |-> priv ] IN
          /\ \E h \in Hash \ {NoHash} :
                /\ ledger' = [ledger EXCEPT ![h] = blk]
                /\ received' = [node \in Node |-> received[node] \cup {h}]
                /\ UNCHANGED lastHash
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
ProcessBlock ==
    /\ \E n \in Node, h \in received[n] :
          /\ ValidBlock(h)
          /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
          /\ UNCHANGED << ledger, lastHash >>

\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesis
    \/ CreateSend
    \/ CreateOpen
    \/ CreateReceive
    \/ CreateChange
    \/ ProcessBlock

\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ lastHash \in Hash
    /\ ledger \in [Hash -> (Block \cup {NoBlockVal})]
    /\ received \in [Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
SafetyInvariant ==
    /\ \A h \in Hash :
          IF ledger[h] # NoBlockVal
          THEN ValidSignature(ledger[h])
          ELSE TRUE

\* ----------------------------------------------------------------------
\* Placeholder implementation for CalculateHashImpl.  The model checker
\* substitutes a concrete, finite implementation via the .cfg file.
CalculateHashImpl(data, prev) == NoHash

============================================================================