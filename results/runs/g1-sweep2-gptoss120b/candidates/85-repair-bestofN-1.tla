---- MODULE SmokeEWD998_SC ----
EXTENDS Naturals, TLC, IOUtils, CSV, Sequences, FiniteSets

\* Filename for the CSV file that appears also in the R script and is passed
\* to the nested TLC instances that are forked below.
CSVFile ==
    "SmokeEWD998_SC" \o ToString(JavaTime) \o ".csv"

\* Write column headers to CSV file at startup of TLC instance that "runs"
\* this script and forks the nested instances of TLC that simulate the spec
\* and collect the statistics.
ASSUME 
    CSVWrite("BugFlags#Violation", <<>>, CSVFile)

\* Command to fork nested TLC instances that simulate the spec and collect the
\* statistics. TLCGet("config").install gives the path to the TLC jar also
\* running this script.
Cmd == LET absolutePathOfTLC == TLCGet("config").install
       IN <<"java", "-jar",
          absolutePathOfTLC, 
          "-noTE",
          "-simulate",
          "SmokeEWD998.tla">>

\* Helper that forces a Boolean result after printing (PrintT returns a string).
PrintOK(p) == PrintT(p) = PrintT(p)

\* Encapsulate the side‑effects (execution, printing, CSV writing) and
\* return TRUE so that the surrounding ASSUME evaluates to a Boolean.
SideEffect(bf) ==
    LET ret == IOEnvExec([BF |-> bf, Out |-> CSVFile,
                          PN |-> RandomElement(3..4)], Cmd) IN
        /\ (CASE ret.exitValue = 0  -> PrintOK(<<JavaTime, bf>>)
            [] ret.exitValue = 10 -> PrintOK(<<bf, "Assumption violation">>)
            [] ret.exitValue = 12 -> PrintOK(<<bf, "Invariant violation (Inv)">>)
            [] ret.exitValue = 13 -> PrintOK(<<bf, "Property violation (TDSpec)">>)
            [] OTHER               -> PrintOK(ret))
        /\ CSVWrite("%1$s#%2$s", <<bf, ret.exitValue>>, CSVFile)
        /\ TRUE

\* Main assumption that drives the external simulations.
ASSUME 
    \A i \in 1..30 :
        \A bf \in SUBSET (1..6) :
            Cardinality(bf) # 1 \/ SideEffect(bf)

===============================================================================