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

ASSUME \A i \in 1..30 : \A bf \in SUBSET (1..6) : Cardinality(bf) # 1
        LET _ == IOEnvExec([BF |-> bf, Out |-> CSVFile, PN |-> RandomElement(3..4)], Cmd)
           IN /\ CSVWrite("%1$s#%2$s", <<bf, "unknown">>) 
              /\ TRUE

====