---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Hash,            \* Set of all possible block hashes
  NoHashVal,       \* Sentinel value for “no hash”
  PrivateKey,      \* Set of all private keys
  PublicKey,       \* Set of all public keys
  Node,            \* Set of network nodes
  GenesisBalance, \* Total coin supply (a natural number)
  NoBlockVal,      \* Sentinel value for “no block”
  CalculateHash,   \* Abstract hash operator (will be overridden)
  NoHash,          \* Alias for NoHashVal (sentinel hash)
  NoBlock          \* Alias for NoBlockVal (sentinel block)

\* ----------------------------------------------------------------------
\* Aliases for the sentinels (useful in the specification)
NoHash == NoHashVal
NoBlock == NoBlockVal

\* ----------------------------------------------------------------------
\* Mappings that are part of the cryptographic setting
\* (these are also constants that must be supplied in the .cfg file)
CONSTANT
  PubKeyOf \in [PrivateKey -> PublicKey]   \* private‑key → public‑key map
  OwnerKey \in [Node -> PrivateKey]       \* node → its private key

\* ----------------------------------------------------------------------
\* Block record definition
Block ==
  [ type       : {"genesis","send","open","receive","change"},
    hash       : Hash,
    prev       : Hash,
    account    : PublicKey,           \* owner of the chain
    signature  : PrivateKey,          \* signer (private key)
    amount     : Nat,                 \* amount transferred (if any)
    dest       : PublicKey,           \* destination account (send)
    source     : Hash,                \* source send block (receive)
    rep        : PublicKey ]          \* new representative (change)

\* Set of possible block values plus the sentinel “no block”
BlockOrNil == Block \cup { NoBlock }

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
  lastHash,   \* the hash of the most recently created block (or NoHash)
  ledger,     \* mapping from hashes to blocks (or NoBlock)
  received    \* per‑node set of hashes that have been broadcast but not yet processed

vars == << lastHash, ledger, received >>

\* ----------------------------------------------------------------------
\* Helper operator: a placeholder implementation for the abstract hash function.
\* The model checker will replace CalculateHash with CalculateHashImpl.
CalculateHashImpl(data, prev) ==
  CHOOSE h \in Hash : TRUE

\* ----------------------------------------------------------------------
\* Initial state
Init ==
  /\ lastHash = NoHash
  /\ ledger   = [h \in Hash |-> NoBlock]
  /\ received = [n \in Node |-> {}]

\* ----------------------------------------------------------------------
\* Action: create the genesis block (can happen only once)
CreateGenesis ==
  /\ lastHash = NoHash
  /\ \E n \in Node :
        LET sk  == OwnerKey[n]                \* private key of creator
            pk  == PubKeyOf[sk]               \* its public key
            h   == CHOOSE h \in Hash : h # NoHash   \* choose a fresh hash
            blk == [ type      |-> "genesis",
                     hash      |-> h,
                     prev      |-> NoHash,
                     account   |-> pk,
                     signature |-> sk,
                     amount    |-> GenesisBalance,
                     dest      |-> NoHash,
                     source    |-> NoHash,
                     rep       |-> NoHash ]
        IN
          /\ lastHash' = h
          /\ ledger'   = [ledger EXCEPT ![h] = blk]
          /\ received' = [n2 \in Node |-> IF n2 = n THEN {} ELSE received[n2] \cup {h}]
          /\ UNCHANGED << >>   \* no other variables
  /\ UNCHANGED << >>   \* ensure no other variable changes

\* ----------------------------------------------------------------------
\* Action: create a send block (simplified – assumes sufficient balance)
CreateSend ==
  /\ lastHash # NoHash
  /\ \E n \in Node :
        LET sk   == OwnerKey[n]
            pk   == PubKeyOf[sk]
            prev == lastHash
            amt  == CHOOSE a \in Nat : a > 0 /\ a <= GenesisBalance   \* nondet amount
            dst  == CHOOSE d \in PublicKey : d # pk                     \* random recipient
            h    == CHOOSE h \in Hash : h # NoHash /\ h # prev
            blk  == [ type      |-> "send",
                      hash      |-> h,
                      prev      |-> prev,
                      account   |-> pk,
                      signature |-> sk,
                      amount    |-> amt,
                      dest      |-> dst,
                      source    |-> NoHash,
                      rep       |-> NoHash ]
        IN
          /\ lastHash' = h
          /\ ledger'   = [ledger EXCEPT ![h] = blk]
          /\ received' = [n2 \in Node |-> IF n2 = n THEN {} ELSE received[n2] \cup {h}]
          /\ UNCHANGED << >>
  /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: create an open block (opens a new account from a received send)
CreateOpen ==
  /\ lastHash # NoHash
  /\ \E n \in Node :
        LET sk   == OwnerKey[n]
            pk   == PubKeyOf[sk]
            src  == CHOOSE s \in Hash : ledger[s] # NoBlock /\ ledger[s].type = "send"
                                         /\ ledger[s].dest = pk
            h    == CHOOSE h \in Hash : h # NoHash /\ h # lastHash
            blk  == [ type      |-> "open",
                      hash      |-> h,
                      prev      |-> NoHash,
                      account   |-> pk,
                      signature |-> sk,
                      amount    |-> ledger[src].amount,
                      dest      |-> NoHash,
                      source    |-> src,
                      rep       |-> NoHash ]
        IN
          /\ lastHash' = h
          /\ ledger'   = [ledger EXCEPT ![h] = blk]
          /\ received' = [n2 \in Node |-> IF n2 = n THEN {} ELSE received[n2] \cup {h}]
          /\ UNCHANGED << >>
  /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: create a receive block (receives a previously sent amount)
CreateReceive ==
  /\ lastHash # NoHash
  /\ \E n \in Node :
        LET sk   == OwnerKey[n]
            pk   == PubKeyOf[sk]
            src  == CHOOSE s \in Hash : ledger[s] # NoBlock /\ ledger[s].type = "send"
                                         /\ ledger[s].dest = pk
            prev == lastHash
            h    == CHOOSE h \in Hash : h # NoHash /\ h # prev
            blk  == [ type      |-> "receive",
                      hash      |-> h,
                      prev      |-> prev,
                      account   |-> pk,
                      signature |-> sk,
                      amount    |-> ledger[src].amount,
                      dest      |-> NoHash,
                      source    |-> src,
                      rep       |-> NoHash ]
        IN
          /\ lastHash' = h
          /\ ledger'   = [ledger EXCEPT ![h] = blk]
          /\ received' = [n2 \in Node |-> IF n2 = n THEN {} ELSE received[n2] \cup {h}]
          /\ UNCHANGED << >>
  /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: create a change‑representative block
CreateChange ==
  /\ lastHash # NoHash
  /\ \E n \in Node :
        LET sk   == OwnerKey[n]
            pk   == PubKeyOf[sk]
            prev == lastHash
            newRep == CHOOSE r \in PublicKey : r # pk
            h    == CHOOSE h \in Hash : h # NoHash /\ h # prev
            blk  == [ type      |-> "change",
                      hash      |-> h,
                      prev      |-> prev,
                      account   |-> pk,
                      signature |-> sk,
                      amount    |-> 0,
                      dest      |-> NoHash,
                      source    |-> NoHash,
                      rep       |-> newRep ]
        IN
          /\ lastHash' = h
          /\ ledger'   = [ledger EXCEPT ![h] = blk]
          /\ received' = [n2 \in Node |-> IF n2 = n THEN {} ELSE received[n2] \cup {h}]
          /\ UNCHANGED << >>
  /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: a node processes a received block (validation stub)
ProcessBlock ==
  /\ \E n \in Node :
        /\ received[n] # {}
        /\ \E h \in received[n] :
              LET blk == ledger[h] IN
                /\ blk # NoBlock
                /\ Verify(blk.signature, blk.account, blk)   \* signature check
                /\ received' = [received EXCEPT ![n] = received[n] \setminus {h}]
                /\ UNCHANGED << lastHash, ledger >>
  /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Verification of a signature (abstract)
Verify(sig, acctPub, blk) ==
  PubKeyOf[sig] = acctPub

\* ----------------------------------------------------------------------
\* The combined next‑state relation
Next ==
  \/ CreateGenesis
  \/ CreateSend
  \/ CreateOpen
  \/ CreateReceive
  \/ CreateChange
  \/ ProcessBlock

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
TypeInvariant ==
  /\ lastHash \in Hash \/ lastHash = NoHash
  /\ ledger \in [Hash -> BlockOrNil]
  /\ received \in [Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* Safety invariant: every stored block has a valid signature
SafetyInvariant ==
  \A h \in Hash :
    IF ledger[h] = NoBlock
       THEN TRUE
       ELSE LET blk == ledger[h] IN Verify(blk.signature, blk.account, blk)

\* ----------------------------------------------------------------------
\* The set of invariants to be checked
INVARIANTS == TypeInvariant /\ SafetyInvariant

====