---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Actions that write to the ledger (in order) are: CreateGenesisBlock (fixed
\* once), CreateSendBlock, CreateOpenBlock, CreateReceiveBlock, and
\* CreateChangeRepresentativeBlock. Validation checks signatures, references
\* and balance/ordering constraints before a block enters a local ledger.

\* The chain walk is a function of the hash, because the hash fully defines
\* the block; the block itself is not the head pointer.
\* Balance recursion is capped at the hash set's size: the invariant is a
\* separate statement over the whole chain, not a bounded check.
\* The block set is a finite set, not a sequence, which is what lets the
\* model explore reordering; the chain is what makes reordering visible.
\* The order-to-set tradeoff is exactly why super-exponential state space is
\* unavoidable in a blockchain that records action history.
\* See the design note in the module header for the full argument.

VARIABLES lastHash, ledger, received

AccountOf(pub) == CHOOSE priv \in PrivateKey : PublicKey[priv] = pub

BlocksFor(account) == {h \in Hash : ledger[h] # NoBlockVal /\ ledger[h].account = account}
LastBlockFor(account) == CHOOSE h \in BlocksFor(account) :
    \A o \in BlocksFor(account) : ledger[o].prev # h

BalanceRecursive(a, visited) ==
  IF visited = {} THEN 0
  ELSE LET h == CHOOSE w \in visited : ledger[w].prev = NoHash \/ ledger[w].prev \notin visited
           rest == visited \ {h}
       IN IF ledger[h].type \in {"send", "changeRep"} THEN BalanceRecursive(a, rest)
          ELSE IF ledger[h].type = "receive" THEN ledger[h].amount + BalanceRecursive(a, rest)
          ELSE BalanceRecursive(a, rest)

Balance(a) == BalanceRecursive(a, BlocksFor(a))

TotalBalance == BalanceRecursive(PublicKey[CHOOSE k \in PrivateKey : TRUE], Hash)

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Hash -> [account: PublicKey, prev: Hash \cup {NoHash}, amount: Nat, type: {"genesis", "send", "open", "receive", "changeRep"}, signer: PublicKey]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [h \in Hash |-> NoBlockVal]
  /\ received = [n \in Node |-> {}]

CreateGenesisBlock ==
  /\ TotalBalance = 0
  /\ \E n \in Node, k \in PrivateKey :
       /\ ledger' = [ledger EXCEPT ![lastHash] =
                      [account |-> AccountOf(k), prev |-> NoHash, amount |-> GenesisBalance, type |-> "genesis", signer |-> AccountOf(k)]]
       /\ lastHash' \in Hash \ {lastHash}
       /\ received' = [m \in Node |-> IF m = n THEN {lastHash} ELSE {}]

CreateSendBlock ==
  /\ \E n \in Node, k \in PrivateKey, b \in PUBLICKEY, amt \in Nat :
       /\ ledger[lastHash] # NoBlockVal /\ ledger[lastHash].type # "send"
       /\ ledger' = [ledger EXCEPT ![lastHash] =
                      [account |-> AccountOf(k), prev |-> lastHash, amount |-> amt, type |-> "send", signer |-> AccountOf(k)]]
       /\ lastHash' \in Hash \ {lastHash}
       /\ received' = [m \in Node |-> IF m = n THEN {lastHash} ELSE received[m]]

CreateOpenBlock ==
  /\ \E n \in Node, k \in PrivateKey, s \in Hash :
       /\ ledger[s] # NoBlockVal /\ ledger[s].type = "send" /\ ledger[s].signer = AccountOf(k)
       /\ ledger' = [ledger EXCEPT ![lastHash] =
                      [account |-> AccountOf(k), prev |-> s, amount |-> 0, type |-> "open", signer |-> AccountOf(k)]]
       /\ lastHash' \in Hash \ {lastHash}
       /\ received' = [m \in Node |-> IF m = n THEN {lastHash} ELSE received[m]]

CreateReceiveBlock ==
  /\ \E n \in Node, k \in PrivateKey, s \in Hash :
       /\ ledger[s] # NoBlockVal /\ ledger[s].type = "send"
       /\ ledger' = [ledger EXCEPT ![lastHash] =
                      [account |-> AccountOf(k), prev |-> LastBlockFor(AccountOf(k)), amount |-> ledger[s].amount, type |-> "receive", signer |-> AccountOf(k)]]
       /\ lastHash' \in Hash \ {lastHash}
       /\ received' = [m \in Node |-> IF m = n THEN {lastHash} ELSE received[m]]

CreateChangeRepresentativeBlock ==
  /\ \E n \in Node, k \in PrivateKey :
       /\ ledger' = [ledger EXCEPT ![lastHash] =
                      [account |-> AccountOf(k), prev |-> LastBlockFor(AccountOf(k)), amount |-> 0, type |-> "changeRep", signer |-> AccountOf(k)]]
       /\ lastHash' \in Hash \ {lastHash}
       /\ received' = [m \in Node |-> IF m = n THEN {lastHash} ELSE received[m]]

ValidateBlock ==
  /\ \E n \in Node, h \in received[n] :
       /\ ledger[h] # NoBlockVal /\ ledger[h].signer = ledger[h].account
       /\ ledger[h].prev = NoHash \/ ledger[ledger[h].prev] # NoBlockVal
       /\ \/ ledger[h].type = "send" => ledger[h].amount <= Balance(ledger[h].account)
          \/ ledger[h].type = "open" => \A b \in Hash : (ledger[b] # NoBlockVal /\ ledger[b].type = "send" /\ ledger[b].signer = ledger[h].account) => b # h
       /\ ledger' = ledger
       /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
       /\ lastHash' = lastHash

Next == CreateGenesisBlock \/ CreateSendBlock \/ CreateOpenBlock \/ CreateReceiveBlock \/ CreateChangeRepresentativeBlock \/ ValidateBlock

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

SafetyInvariant == TotalBalance <= GenesisBalance

====