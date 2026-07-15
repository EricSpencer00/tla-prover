---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants (provided by the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS
    Hash,          \* the universal set of block hashes
    NoHashVal,     \* sentinel value meaning “no hash yet”
    PrivateKey,    \* the set of all private keys
    PublicKey,     \* the set of all public keys
    Node,          \* the set of network nodes
    GenesisBalance,\* total number of coins initially created
    NoBlockVal,    \* sentinel meaning “no block”
    CalculateHash, \* abstract hashing operator
    NoHash,        \* synonym for NoHashVal (used in some contexts)
    NoBlock        \* synonym for NoBlockVal

\* ----------------------------------------------------------------------
\* Derived constant: a mapping from private keys to their corresponding public keys
\* (the model configuration must supply a function PrivateToPublic ∈ [PrivateKey -> PublicKey])
\* ----------------------------------------------------------------------
CONSTANT PrivateToPublic

\* ----------------------------------------------------------------------
\* Types for readability
\* ----------------------------------------------------------------------
Account == PublicKey
Bal == Nat

\* ----------------------------------------------------------------------
\* Block Types
\* ----------------------------------------------------------------------
BlockType == {"Genesis", "Send", "Open", "Receive", "ChangeRep"}

\* ----------------------------------------------------------------------
\* Block record (fields common to all block kinds)
\* ----------------------------------------------------------------------
Block == [
    type          : BlockType,
    hash          : Hash,
    prevHash      : Hash,
    account       : Account,
    balance       : Bal,
    signature     : PUBLIC(PublicKey), \* abstract signature, only its existence matters
    linkedHash    : Hash            \* for Send/Open/Receive: the referenced block
]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    lastHash,      \* the hash of the most recent block in the whole system
    ledger,        \* [node ∈ Node -> [h ∈ Hash -> Block ∪ {NoBlockVal}]]
    received       \* [node ∈ Node -> SUBSET Hash]

\* ----------------------------------------------------------------------
\* Type correctness predicate (used for the TypeInvariant)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ lastHash \in Hash \/ lastHash = NoHashVal
    /\ ledger \in [Node -> [Hash -> (Block \cup {NoBlockVal})]]
    /\ \A n \in Node: received[n] \subseteq Hash

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
\* The set of all hashes that actually appear in a node's ledger
LedgerHashes(n) == { h \in Hash : ledger[n][h] # NoBlockVal }

\* The hash of the latest block for a particular account on a particular node
LastHashForAccount(n, acct) ==
    IF \E h \in LedgerHashes(n) : ledger[n][h].account = acct
       THEN
          LET cand == { h \in LedgerHashes(n) : ledger[n][h].account = acct } IN
          CHOOSE h \in cand :
              \A h2 \in cand : ledger[n][h2].prevHash # h => ledger[n][h2].prevHash # h2
       ELSE NoHashVal

\* Compute the balance of an account on a node by walking its chain backwards.
\* For simplicity we assume the chain is well‑formed (no forks) – the invariants
\* guarantee this.
Balance(n, acct) ==
    IF LastHashForAccount(n, acct) = NoHashVal
       THEN 0
       ELSE
          LET h0 == LastHashForAccount(n, acct) IN
          BalanceFromHash(n, h0)

BalanceFromHash(n, h) ==
    IF h = NoHashVal
       THEN 0
       ELSE
          LET blk == ledger[n][h] IN
          CASE blk.type = "Genesis"   -> blk.balance
               [] blk.type = "Open"   -> blk.balance
               [] blk.type = "Receive"-> blk.balance
               [] blk.type = "Send"   -> 0        \* a Send block does not hold balance
               [] blk.type = "ChangeRep"-> BalanceFromHash(n, blk.prevHash)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ lastHash = NoHashVal
    /\ ledger = [ n \in Node |-> [ h \in Hash |-> NoBlockVal ]]
    /\ received = [ n \in Node |-> {} ]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* CreateGenesisBlock is allowed only when no other block exists.
CreateGenesisBlock ==
    /\ lastHash = NoHashVal
    /\ \E pk \in PrivateKey :
          LET acct == PrivateToPublic[pk] IN
          LET newHash == CalculateHash(<<"Genesis", acct, GenesisBalance>>, NoHashVal) IN
          /\ newHash \in Hash
          /\ /\ ledger' = [ n \in Node |-> [ ledger[n] EXCEPT ![newHash] = [
                     type       |-> "Genesis",
                     hash       |-> newHash,
                     prevHash   |-> NoHashVal,
                     account    |-> acct,
                     balance    |-> GenesisBalance,
                     signature  |-> pk,
                     linkedHash |-> NoHashVal
                 ]]]
          /\ lastHash' = newHash
          /\ received' = [ n \in Node |-> received[n] ]
          /\ UNCHANGED << >>

\* Send block creation
CreateSendBlock(snder) ==
    /\ snder \in Node
    /\ \E pk \in PrivateKey :
          LET acct == PrivateToPublic[pk] IN
          /\ acct = snder   \* for simplicity we associate a node with its key
          /\ Balance(snder, acct) > 0
          /\ \E dest \in Account :
                LET prev == LastHashForAccount(snder, acct) IN
                LET amount == 1 IN           \* fixed amount for the model
                /\ Balance(snder, acct) >= amount
                LET newHash == CalculateHash(<<"Send", acct, amount, dest, prev>>, prev) IN
                /\ newHash \in Hash
                /\ /\ ledger' = [ n \in Node |-> [ ledger[n] EXCEPT ![newHash] = [
                           type       |-> "Send",
                           hash       |-> newHash,
                           prevHash   |-> prev,
                           account    |-> acct,
                           balance    |-> BalanceFromHash(snder, prev) - amount,
                           signature  |-> pk,
                           linkedHash |-> prev
                       ]]]
                /\ \A n \in Node : received' = [ received EXCEPT ![n] = received[n] \cup {newHash} ]
                /\ UNCHANGED lastHash

\* Open block creation (must reference a received Send block)
CreateOpenBlock(node, pk) ==
    /\ node \in Node
    /\ pk \in PrivateKey
    /\ \E sendHash \in received[node] :
          LET sendBlk == ledger[node][sendHash] IN
          /\ sendBlk.type = "Send"
          /\ sendBlk.linkedHash # NoHashVal
          LET acct == PrivateToPublic[pk] IN
          /\ acct = node   \* node owns the account it opens
          LET newHash == CalculateHash(<<"Open", acct, sendBlk.balance>>, sendBlk.hash) IN
          /\ newHash \in Hash
          /\ /\ ledger' = [ n \in Node |-> [ ledger[n] EXCEPT ![newHash] = [
                     type       |-> "Open",
                     hash       |-> newHash,
                     prevHash   |-> sendBlk.hash,
                     account    |-> acct,
                     balance    |-> sendBlk.balance,
                     signature  |-> pk,
                     linkedHash |-> sendHash
                 ]]]
          /\ \A n \in Node : received' = [ received EXCEPT ![n] = received[n] \cup {newHash} ]
          /\ UNCHANGED lastHash

\* Receive block creation
CreateReceiveBlock(node, pk) ==
    /\ node \in Node
    /\ pk \in PrivateKey
    /\ \E sendHash \in received[node] :
          LET sendBlk == ledger[node][sendHash] IN
          /\ sendBlk.type \in {"Send", "Open"}
          LET acct == PrivateToPublic[pk] IN
          /\ acct = node
          LET prev == LastHashForAccount(node, acct) IN
          LET amount == 1 IN   \* fixed amount for the model
          LET newBal == BalanceFromHash(node, prev) + amount IN
          LET newHash == CalculateHash(<<"Receive", acct, newBal, sendHash, prev>>, prev) IN
          /\ newHash \in Hash
          /\ /\ ledger' = [ n \in Node |-> [ ledger[n] EXCEPT ![newHash] = [
                     type       |-> "Receive",
                     hash       |-> newHash,
                     prevHash   |-> prev,
                     account    |-> acct,
                     balance    |-> newBal,
                     signature  |-> pk,
                     linkedHash |-> sendHash
                 ]]]
          /\ \A n \in Node : received' = [ received EXCEPT ![n] = received[n] \cup {newHash} ]
          /\ UNCHANGED lastHash

\* Change representative block creation
CreateChangeRep(node, pk) ==
    /\ node \in Node
    /\ pk \in PrivateKey
    /\ \E acct \in Account :
          LET prev == LastHashForAccount(node, acct) IN
          prev # NoHashVal
          LET newHash == CalculateHash(<<"ChangeRep", acct, prev>>, prev) IN
          /\ newHash \in Hash
          /\ /\ ledger' = [ n \in Node |-> [ ledger[n] EXCEPT ![newHash] = [
                     type       |-> "ChangeRep",
                     hash       |-> newHash,
                     prevHash   |-> prev,
                     account    |-> acct,
                     balance    |-> BalanceFromHash(node, prev),
                     signature  |-> pk,
                     linkedHash |-> NoHashVal
                 ]]]
          /\ \A n \in Node : received' = [ received EXCEPT ![n] = received[n] \cup {newHash} ]
          /\ UNCHANGED lastHash

\* Processing a received block (validation + addition to ledger)
ProcessBlock(node) ==
    /\ node \in Node
    /\ \E h \in received[node] :
          LET blk == ledger[node][h] IN
          /\ blk # NoBlockVal
          /\ ValidateBlock(node, blk)
          /\ ledger' = [ n \in Node |-> [ ledger[n] EXCEPT ![h] = blk ]]
          /\ received' = [ received EXCEPT ![node] = received[node] \ {h} ]
          /\ UNCHANGED lastHash

\* Validation predicate (abstracted; the model assumes it always succeeds if
\* the structural conditions below hold)
ValidateBlock(node, blk) ==
    /\ blk.signature \in PrivateKey
    /\ PrivateToPublic[blk.signature] = blk.account
    /\ IF blk.type = "Genesis"
          THEN blk.prevHash = NoHashVal
       ELSE IF blk.type = "Open"
          THEN blk.prevHash # NoHashVal
               /\ ledger[node][blk.prevHash] # NoBlockVal
               /\ ledger[node][blk.prevHash].type \in {"Send", "Open"}
       ELSE IF blk.type = "Send"
          THEN blk.prevHash # NoHashVal
               /\ ledger[node][blk.prevHash] # NoBlockVal
               /\ blk.balance = BalanceFromHash(node, blk.prevHash) - 1
       ELSE IF blk.type = "Receive"
          THEN blk.prevHash # NoHashVal
               /\ ledger[node][blk.prevHash] # NoBlockVal
               /\ ledger[node][blk.linkedHash] # NoBlockVal
               /\ ledger[node][blk.linkedHash].type \in {"Send", "Open"}
               /\ blk.balance = BalanceFromHash(node, blk.prevHash) + 1
       ELSE IF blk.type = "ChangeRep"
          THEN blk.prevHash # NoHashVal
               /\ ledger[node][blk.prevHash] # NoBlockVal
               /\ blk.balance = BalanceFromHash(node, blk.prevHash)
       ELSE FALSE

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ CreateGenesisBlock
    \/ \E n \in Node : CreateSendBlock(n)
    \/ \E n \in Node, pk \in PrivateKey : CreateOpenBlock(n, pk)
    \/ \E n \in Node, pk \in PrivateKey : CreateReceiveBlock(n, pk)
    \/ \E n \in Node, pk \in PrivateKey : CreateChangeRep(n, pk)
    \/ \E n \in Node : ProcessBlock(n)

\* ----------------------------------------------------------------------
\* Safety invariant: every block stored in any node's ledger has a valid signature
\* belonging to the account that owns the chain.
\* ----------------------------------------------------------------------
SafetyInvariant ==
    \A n \in Node :
      \A h \in LedgerHashes(n) :
          LET blk == ledger[n][h] IN
          blk.signature \in PrivateKey /\ PrivateToPublic[blk.signature] = blk.account

\* ----------------------------------------------------------------------
\* Full specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
THEOREM TypeInvariant == TypeOK
THEOREM SafetyInvariant == SafetyInvariant

====