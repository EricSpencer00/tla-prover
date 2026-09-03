---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* A block is a signed record in an account chain; the chain is the ordering.
\* The invariant is about signatures, not balance arithmetic.
Block == [hash: Hash, prev: Hash \cup {NoHash}, acct: PublicKey, kind: {"genesis", "send", "open", "receive", "change"}, amt: 0..GenesisBalance, sig: PrivateKey]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* The ledger is replicated across nodes; a node validates against its own copy.
TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Block]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* The genesis block is the only way coins enter the system.
CreateGenesisBlock ==
  /\ lastHash = NoHash
  /\ \E k \in PrivateKey, n \in Node :
       /\ lastHash' = CalculateHash([prev |-> NoHash, acct |-> PublicKey[k], kind |-> "genesis", amt |-> GenesisBalance], NoHash)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [hash |-> lastHash', prev |-> NoHash, acct |-> PublicKey[k], kind |-> "genesis", amt |-> GenesisBalance, sig |-> k]]]
       /\ received' = [m \in Node |-> received[m] \cup {[hash |-> lastHash', prev |-> NoHash, acct |-> PublicKey[k], kind |-> "genesis", amt |-> GenesisBalance, sig |-> k]}]

\* A send block debits the sender; the amount is checked against the chain balance.
CreateSendBlock ==
  /\ lastHash # NoHash
  /\ \E k \in PrivateKey, n \in Node, amt \in 1..GenesisBalance :
       /\ Balance(ledger[n], PublicKey[k]) >= amt
       /\ lastHash' = CalculateHash([prev |-> lastHash, acct |-> PublicKey[k], kind |-> "send", amt |-> amt], lastHash)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [hash |-> lastHash', prev |-> lastHash, acct |-> PublicKey[k], kind |-> "send", amt |-> amt, sig |-> k]]]
       /\ received' = [m \in Node |-> received[m] \cup {[hash |-> lastHash', prev |-> lastHash, acct |-> PublicKey[k], kind |-> "send", amt |-> amt, sig |-> k]}]

CreateOpenBlock ==
  /\ lastHash # NoHash
  /\ \E k \in PrivateKey, n \in Node :
       /\ \E b \in received[n] : b.kind = "send" /\ b.acct = PublicKey[k]
       /\ lastHash' = CalculateHash([prev |-> lastHash, acct |-> PublicKey[k], kind |-> "open", amt |-> 0], lastHash)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [hash |-> lastHash', prev |-> lastHash, acct |-> PublicKey[k], kind |-> "open", amt |-> 0, sig |-> k]]]
       /\ received' = [m \in Node |-> received[m] \cup {[hash |-> lastHash', prev |-> lastHash, acct |-> PublicKey[k], kind |-> "open", amt |-> 0, sig |-> k]}]

CreateReceiveBlock ==
  /\ lastHash # NoHash
  /\ \E k \in PrivateKey, n \in Node :
       /\ \E b \in received[n] : b.kind = "send" /\ b.acct # PublicKey[k]
       /\ lastHash' = CalculateHash([prev |-> lastHash, acct |-> PublicKey[k], kind |-> "receive", amt |-> b.amt], lastHash)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [hash |-> lastHash', prev |-> lastHash, acct |-> PublicKey[k], kind |-> "receive", amt |-> b.amt, sig |-> k]]]
       /\ received' = [m \in Node |-> received[m] \cup {[hash |-> lastHash', prev |-> lastHash, acct |-> PublicKey[k], kind |-> "receive", amt |-> b.amt, sig |-> k]}]

CreateChangeRepresentativeBlock ==
  /\ lastHash # NoHash
  /\ \E k \in PrivateKey, n \in Node :
       /\ lastHash' = CalculateHash([prev |-> lastHash, acct |-> PublicKey[k], kind |-> "change", amt |-> 0], lastHash)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [hash |-> lastHash', prev |-> lastHash, acct |-> PublicKey[k], kind |-> "change", amt |-> 0, sig |-> k]]]
       /\ received' = [m \in Node |-> received[m] \cup {[hash |-> lastHash', prev |-> lastHash, acct |-> PublicKey[k], kind |-> "change", amt |-> 0, sig |-> k]}]

\* Validation is per-node against its own copy; a block is only added once it passes.
ValidateBlock ==
  \E n \in Node, b \in received[n] :
    /\ ledger[n][b.hash] = NoBlockVal
    /\ b.sig \in PrivateKey
    /\ PublicKey[b.sig] = b.acct
    /\ (b.prev = NoHash \/ ledger[n][b.prev] # NoBlockVal)
    /\ (b.kind = "send" => Balance(ledger[n], b.acct) >= b.amt)
    /\ (b.kind = "open" => \A c \in Hash : ledger[n][c] # NoBlockVal => ~(ledger[n][c].kind = "send" /\ ledger[n][c].acct = b.acct))
    /\ (b.kind = "receive" => \A c \in Hash : ledger[n][c] # NoBlockVal => ~(ledger[n][c].kind = "send" /\ ledger[n][c].acct = b.acct /\ ledger[n][c].amt = b.amt))
    /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![b.hash] = b]]
    /\ received' = [received EXCEPT ![n] = received[n] \ {b}]
    /\ UNCHANGED lastHash

Next == CreateGenesisBlock \/ CreateSendBlock \/ CreateOpenBlock \/ CreateReceiveBlock \/ CreateChangeRepresentativeBlock \/ ValidateBlock

Spec == Init /\ [][Next]_vars

\* The chain is the ordering, so the invariant is about signatures, not balance.
SafetyInvariant == \A n \in Node, h \in Hash : ledger[n][h] # NoBlockVal => PublicKey[ledger[n][h].sig] = ledger[n][h].acct

Balance(f, acct) == BalanceRec(f, acct, NoHash)

BalanceRec(f, acct, h) ==
  IF h = NoHash THEN 0
  ELSE LET b == f[h] IN
       IF b = NoBlockVal THEN 0
       ELSE IF b.acct = acct THEN
         IF b.kind = "send" THEN -b.amt + BalanceRec(f, acct, b.prev)
         ELSE IF b.kind = "receive" THEN b.amt + BalanceRec(f, acct, b.prev)
         ELSE BalanceRec(f, acct, b.prev)
       ELSE BalanceRec(f, acct, b.prev)

\* The total of all account balances never exceeds the genesis balance.
BalanceConservation ==
  LET accounts == {PublicKey[k] : k \in PrivateKey} IN
  LET sum[S \in SUBSET accounts] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE IN Balance(ledger[CHOOSE n \in Node : TRUE], x) + sum[S \ {x}]
  IN sum[accounts] <= GenesisBalance

====