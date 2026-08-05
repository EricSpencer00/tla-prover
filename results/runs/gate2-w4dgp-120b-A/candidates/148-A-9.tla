---- MODULE Nano ----
EXTENDS Naturals, Sequences

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal

\* CalculateHash is a named constant rather than a plain operator, because the
\* reference .cfg substitutes a different implementation for it when it runs
\* TLC versus when the module is opened in the IDE.
CONSTANT CalculateHash

NoHash == NoHashVal
NoBlock == NoBlockVal

\* Each account is identified by its signing key.
Account == PublicKey

VARIABLES lastHash, ledger, seen
vars == <<lastHash, ledger, seen>>

\* The block lattice records action history directly, so the count of blocks
\* and the depth of each account chain are themselves a source of state explosion.
RECURSIVE BalanceOf(_)
BalanceOf(chain) ==
    IF chain = <<>> THEN 0
    ELSE LET a == Head(chain) IN
         (IF a.type = "send" THEN -a.amount ELSE IF a.type = "receive" THEN a.amount ELSE 0) + BalanceOf(Tail(chain))

\* The balance of an account is its genesis amount plus whatever its private
\* chain has netted; every block carries the previous hash of that chain.
RECURSIVE ChainFor(_, _, _)
ChainFor(acc, hashes, id) ==
    IF hashes = {} THEN <<>>
    ELSE IF id \notin hashes THEN ChainFor(acc, hashes \ {id}, id)
    ELSE LET b == ledger[id] IN
         IF b.account = acc /\ b.prev = NoHash THEN <<b>>
         ELSE IF b.account = acc /\ b.prev # NoHash /\ b.prev \in hashes
              THEN ChainFor(acc, hashes, b.prev) \o <<b>>
         ELSE ChainFor(acc, hashes, id)

RECURSIVE AccountBalance(_)
AccountBalance(acc) == BalanceOf(ChainFor(acc, DOMAIN ledger, NoHash))

RECURSIVE SumBalances(_)
SumBalances(s) ==
    IF s = {} THEN 0
    ELSE LET x == CHOOSE y \in s : TRUE IN AccountBalance(x) + SumBalances(s \ {x})

Init ==
    /\ lastHash = NoHash
    /\ ledger = [h \in Hash |-> NoBlock]
    /\ seen = [n \in Node |-> {}]

\* Genesis block: the one-time creation of the initial coin supply.
CreateGenesis(n) ==
    /\ lastHash = NoHash
    /\ LET b == [type |-> "genesis", account |-> CHOOSE k \in PrivateKey : TRUE,
                 prev |-> NoHash, amount |-> GenesisBalance,
                 sig |-> "sig:account:None:" : CHOOSE k \in PrivateKey : TRUE] IN
       /\ CalculateHash(b) # NoHash
       /\ lastHash' = CalculateHash(b)
       /\ ledger' = [ledger EXCEPT ![CalculateHash(b)] = b]
    /\ seen' = [n \in Node |-> seen[n] \cup {CalculateHash(b)}]
    /\ UNCHANGED <<>>

\* Send block: moves funds out of an account, appending to its private chain.
CreateSend(n, recPub, amt) ==
    /\ LET b == [type |-> "send", account |-> n,
                 prev |-> lastHash, amount |-> amt,
                 sig |-> "sig:" + n + ":" + (IF lastHash = NoHash THEN "None" ELSE lastHash)] IN
       /\ CalculateHash(b) # NoHash
       /\ AccountBalance(n) >= amt
       /\ lastHash' = CalculateHash(b)
       /\ ledger' = [ledger EXCEPT ![CalculateHash(b)] = b]
    /\ seen' = [n \in Node |-> seen[n] \cup {CalculateHash(b)}]
    /\ UNCHANGED <<>>

\* Open block: establishes a new account's first block, referencing the send
\* that created it.
CreateOpen(n, sendId) ==
    /\ sendId \in DOMAIN ledger /\ ledger[sendId].type = "send" /\ ledger[sendId].account # n
    /\ LET b == [type |-> "open", account |-> n,
                 prev |-> NoHash, amount |-> 0, ref |-> sendId,
                 sig |-> "sig:" + n + ":None"] IN
       /\ CalculateHash(b) # NoHash
       /\ lastHash' = CalculateHash(b)
       /\ ledger' = [ledger EXCEPT ![CalculateHash(b)] = b]
    /\ seen' = [n \in Node |-> seen[n] \cup {CalculateHash(b)}]
    /\ UNCHANGED <<>>

\* Receive block: incorporates a pending incoming send into an account's chain.
CreateReceive(n, sendId) ==
    /\ sendId \in DOMAIN ledger /\ ledger[sendId].type = "send" /\ ledger[sendId].account # n
    /\ LET b == [type |-> "receive", account |-> n,
                 prev |-> lastHash, amount |-> 0, ref |-> sendId,
                 sig |-> "sig:" + n + ":" + (IF lastHash = NoHash THEN "None" ELSE lastHash)] IN
       /\ CalculateHash(b) # NoHash
       /\ lastHash' = CalculateHash(b)
       /\ ledger' = [ledger EXCEPT ![CalculateHash(b)] = b]
    /\ seen' = [n \in Node |-> seen[n] \cup {CalculateHash(b)}]
    /\ UNCHANGED <<>>

\* Change block: a node rotates its voting representative, appending to its chain.
CreateChange(n, repKey) ==
    /\ LET b == [type |-> "change", account |-> n,
                 prev |-> lastHash, amount |-> 0, ref |-> repKey,
                 sig |-> "sig:" + n + ":" + (IF lastHash = NoHash THEN "None" ELSE lastHash)] IN
       /\ CalculateHash(b) # NoHash
       /\ lastHash' = CalculateHash(b)
       /\ ledger' = [ledger EXCEPT ![CalculateHash(b)] = b]
    /\ seen' = [n \in Node |-> seen[n] \cup {CalculateHash(b)}]
    /\ UNCHANGED <<>>

ValidateBlock(b) ==
    /\ b.sig = "sig:" + b.account + ":" + (IF b.prev = NoHash THEN "None" ELSE b.prev)
    /\ (b.type = "genesis" => TRUE)
    /\ (b.type \in {"send", "receive"} => b.amount \in Nat)
    /\ b.prev = NoHash \/ (b.prev \in DOMAIN ledger /\ ledger[b.prev].account = b.account)
    /\ (b.type = "send" => AccountBalance(b.account) >= b.amount)
    /\ (b.type = "open" => b.ref \in DOMAIN ledger /\ ledger[b.ref].type = "send"
                             /\ ledger[b.ref].account # b.account)
    /\ (b.type = "receive" => b.ref \in DOMAIN ledger /\ ledger[b.ref].type = "send"
                               /\ ledger[b.ref].account # b.account)

ProcessSeen(n) ==
    /\ \E h \in seen[n] :
         /\ ledger[h] = NoBlock
         /\ ValidateBlock(ledger[h])
         /\ ledger' = [ledger EXCEPT ![h] = ledger[h]]
         /\ seen' = [seen EXCEPT ![n] = seen[n] \ {h}]
    /\ UNCHANGED lastHash

Next ==
    \/ \E n \in Node : CreateGenesis(n)
    \/ \E n \in Node, recPub \in PublicKey, amt \in Nat : CreateSend(n, recPub, amt)
    \/ \E n \in Node, sendId \in Hash : CreateOpen(n, sendId)
    \/ \E n \in Node, sendId \in Hash : CreateReceive(n, sendId)
    \/ \E n \in Node, repKey \in PublicKey : CreateChange(n, repKey)
    \/ \E n \in Node : ProcessSeen(n)

Spec == Init /\ [][Next]_vars

\* A block in the ledger must be an authentic Ed25519 signature from the owner
\* of the account chain that block lives in.
TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Hash -> NoBlock \cup {[type : {"genesis", "send", "receive", "open", "change"},
                                         account : Account, prev : Hash \cup {NoHash},
                                         amount : Nat, ref : PublicKey \cup {NoHash}, sig : STRING}]]

SafetyInvariant ==
    \A h \in Hash : ledger[h] # NoBlock =>
        ledger[h].sig = "sig:" + ledger[h].account + ":" + (IF ledger[h].prev = NoHash THEN "None" ELSE ledger[h].prev)

====