---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* The Nano blockchain uses a block-lattice: each account has its own chain of blocks.
\* This spec models the hash and signature aspects of that protocol, and shows how
\* finite model checking struggles with blockchains whose state space grows
\* super-exponentially (the chain itself records action order).

VARIABLES
  lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* A block is a record of the account it belongs to, the previous block in that
\* account's chain, the block it references (for sends/receives), the amount it
\* moves, the block type, and the signature over the block's contents.
Block == [account: PublicKey, prev: Hash, ref: Hash, amount: Nat, kind: {"genesis", "send", "open", "receive", "change"}, sig: PrivateKey]

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

\* Balance is computed by walking an account's chain backwards from its tip.
RECURSIVE Balance(_)
Balance(h) ==
  IF h = NoHashVal THEN 0
  ELSE LET b == ledger[CHOOSE n \in Node : ledger[n][h] # NoBlockVal] IN
       IF b.kind = "receive" THEN Balance(b.prev) + b.amount
       ELSE Balance(b.prev)

\* The total balance across all accounts must never exceed the genesis balance.
BalanceInvariant ==
  LET accounts == {ledger[n][h].account : n \in Node, h \in Hash, ledger[n][h] # NoBlockVal} IN
  LET sum == (CHOOSE s \in Nat : \E f \in [accounts -> Nat] : (\A a \in accounts : f[a] = Balance(f[a])) /\ s = (CHOOSE x \in Nat : \A y \in accounts : y = x))
  IN sum <= GenesisBalance

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* The hash of a block is derived from its contents and the previous hash.
HashOf(b) == CalculateHash(b, lastHash)

\* A block is valid if its signature matches the account's public key and its
\* referenced blocks exist in the local ledger copy.
ValidBlock(b, n) ==
  /\ b.sig = CHOOSE k \in PrivateKey : k \in {n} /\ CHOOSE p \in PublicKey : p \in {b.account}
  /\ (b.prev = NoHashVal \/ \E m \in Node : ledger[m][b.prev] # NoBlockVal)
  /\ (b.ref = NoHashVal \/ \E m \in Node : ledger[m][b.ref] # NoBlockVal)
  /\ (b.kind = "send" => b.amount > 0 /\ b.amount <= Balance(b.prev))
  /\ (b.kind = "open" => b.prev = NoHashVal /\ b.ref # NoHashVal /\ ledger[CHOOSE m \in Node : ledger[m][b.ref] # NoBlockVal][b.ref].account # b.account)
  /\ (b.kind = "receive" => b.prev # NoHashVal /\ b.ref # NoHashVal /\ ledger[CHOOSE m \in Node : ledger[m][b.ref] # NoBlockVal][b.ref].account # b.account)

\* The genesis block is created once and added to every node's ledger at once.
CreateGenesisBlock(n) ==
  /\ lastHash = NoHashVal
  /\ \A m \in Node : ledger[m][HashOf([account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> NoHashVal, ref |-> NoHashVal, amount |-> GenesisBalance, kind |-> "genesis", sig |-> n])] = NoBlockVal
  /\ lastHash' = HashOf([account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> NoHashVal, ref |-> NoHashVal, amount |-> GenesisBalance, kind |-> "genesis", sig |-> n])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![HashOf([account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> NoHashVal, ref |-> NoHashVal, amount |-> GenesisBalance, kind |-> "genesis", sig |-> n])]] = [account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> NoHashVal, ref |-> NoHashVal, amount |-> GenesisBalance, kind |-> "genesis", sig |-> n]]
  /\ received' = [m \in Node |-> received[m]]

\* A send block reduces the sender's balance and names a recipient.
CreateSendBlock(n, to, amt) ==
  /\ lastHash # NoHashVal
  /\ \E m \in Node : ledger[m][lastHash] # NoBlockVal /\ ledger[m][lastHash].account = CHOOSE p \in PublicKey : p \in {b.account}
  /\ amt > 0 /\ amt <= Balance(lastHash)
  /\ lastHash' = HashOf([account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> lastHash, ref |-> to, amount |-> amt, kind |-> "send", sig |-> n])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![HashOf([account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> lastHash, ref |-> to, amount |-> amt, kind |-> "send", sig |-> n])]] = [account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> lastHash, ref |-> to, amount |-> amt, kind |-> "send", sig |-> n]]
  /\ received' = [m \in Node |-> received[m] \cup {HashOf([account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> lastHash, ref |-> to, amount |-> amt, kind |-> "send", sig |-> n])}]

\* An open block starts a new account's chain from a send directed to it.
CreateOpenBlock(n, sendHash) ==
  /\ lastHash # NoHashVal
  /\ \E m \in Node : ledger[m][sendHash] # NoBlockVal /\ ledger[m][sendHash].kind = "send" /\ ledger[m][sendHash].ref = CHOOSE p \in PublicKey : p \in {b.account}
  /\ lastHash' = HashOf([account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> NoHashVal, ref |-> sendHash, amount |-> 0, kind |-> "open", sig |-> n])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![HashOf([account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> NoHashVal, ref |-> sendHash, amount |-> 0, kind |-> "open", sig |-> n])]] = [account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> NoHashVal, ref |-> sendHash, amount |-> 0, kind |-> "open", sig |-> n]]
  /\ received' = [m \in Node |-> received[m] \cup {HashOf([account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> NoHashVal, ref |-> sendHash, amount |-> 0, kind |-> "open", sig |-> n])}]

\* A receive block adds the amount from a send block to the receiver's balance.
CreateReceiveBlock(n, sendHash) ==
  /\ lastHash # NoHashVal
  /\ \E m \in Node : ledger[m][sendHash] # NoBlockVal /\ ledger[m][sendHash].kind = "send" /\ ledger[m][sendHash].ref = CHOOSE p \in PublicKey : p \in {b.account}
  /\ lastHash' = HashOf([account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> lastHash, ref |-> sendHash, amount |-> ledger[CHOOSE m \in Node : ledger[m][sendHash] # NoBlockVal][sendHash].amount, kind |-> "receive", sig |-> n])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![HashOf([account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> lastHash, ref |-> sendHash, amount |-> ledger[CHOOSE m \in Node : ledger[m][sendHash] # NoBlockVal][sendHash].amount, kind |-> "receive", sig |-> n])]] = [account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> lastHash, ref |-> sendHash, amount |-> ledger[CHOOSE m \in Node : ledger[m][sendHash] # NoBlockVal][sendHash].amount, kind |-> "receive", sig |-> n]]
  /\ received' = [m \in Node |-> received[m] \cup {HashOf([account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> lastHash, ref |-> sendHash, amount |-> ledger[CHOOSE m \in Node : ledger[m][sendHash] # NoBlockVal][sendHash].amount, kind |-> "receive", sig |-> n])}]

\* A change-representative block updates the voting representative.
CreateChangeBlock(n) ==
  /\ lastHash # NoHashVal
  /\ lastHash' = HashOf([account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> lastHash, ref |-> NoHashVal, amount |-> 0, kind |-> "change", sig |-> n])
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![HashOf([account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> lastHash, ref |-> NoHashVal, amount |-> 0, kind |-> "change", sig |-> n])]] = [account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> lastHash, ref |-> NoHashVal, amount |-> 0, kind |-> "change", sig |-> n]]
  /\ received' = [m \in Node |-> received[m] \cup {HashOf([account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> lastHash, ref |-> NoHashVal, amount |-> 0, kind |-> "change", sig |-> n])}]

\* A node validates a received block against its own ledger copy and adds it.
ValidateBlock(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] = NoBlockVal
  /\ \E b \in Block : b = [account |-> CHOOSE p \in PublicKey : p \in {b.account}, prev |-> NoHashVal, ref |-> NoHashVal, amount |-> 0, kind |-> "genesis", sig |-> n]
  /\ ValidBlock(b, n)
  /\ ledger' = [ledger EXCEPT ![n][h] = b]
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E n \in Node : CreateGenesisBlock(n)
  \/ \E n \in Node, to \in PublicKey, amt \in Nat : CreateSendBlock(n, to, amt)
  \/ \E n \in Node, sendHash \in Hash : CreateOpenBlock(n, sendHash)
  \/ \E n \in Node, sendHash \in Hash : CreateReceiveBlock(n, sendHash)
  \/ \E n \in Node : CreateChangeBlock(n)
  \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

\* Every block in every node's ledger copy must have a valid signature.
SafetyInvariant ==
  \A n \in Node, h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].sig = CHOOSE k \in PrivateKey : k \in {n} /\ CHOOSE p \in PublicKey : p \in {ledger[n][h].account}

====