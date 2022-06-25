---- MODULE Raft ----
\* Formal specification for the Raft consensus algorithm.
\*
\* Original document is by Diego Ongaro, 2014 (CC BY-4.0).
\* Source: https://github.com/ongardie/raft.tla
\* Please check https://creativecommons.org/licenses/by/4.0 for more information.
\* This document includes some adaptions by Yuya Shiratori.
\*
\* Changes:
\*   - Change the format
\*   - Annotate types for Apalache
\*   - Change the type of the variable `votedFor` from `Server \cup { Nil }` to `Seq(SERVER)`
\*   - Use `clientRequest` instead of `v \in Value` (thanks to @jinlmsft)
\*

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    \* The set of server IDs
    \* @type: Set(SERVER);
    Server

CONSTANTS
    \* Server states.
    \* @type: STATE;
    Follower,
    \* @type: STATE;
    Candidate,
    \* @type: STATE;
    Leader

----
\* Global variables

\* The type representing both requests and responses sent from a server.
\* @typeAlias: MESSAGE = [];
MSGTypeAliases == TRUE

VARIABLES
    \* A bag of records representing requests and responses sent from one server
    \* to another.
    \* @type: MESSAGE -> Int;
    messages

----
\* The following variables are all per server.

VARIABLES
    \* The server's state (Follower, Candidate, or Leader).
    \* @type: SERVER -> STATE;
    state

\* @type: <<SERVER -> STATE>>;
serverVars == <<state>>

----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, serverVars>>

----
\* Define initial values for all variables

\* @type: Bool;
InitServerVars == state = [i \in Server |-> Follower]

\* @type: Bool;
Init == /\ messages = [m \in {} |-> 0]
        /\ InitServerVars

----
\* Defines how the variables may transition.
\* @type: Bool;
Next == UNCHANGED <<messages, serverVars>>

\* The specification must start with the initial state and transition according
\* to Next.
\* @type: Bool;
Spec == Init /\ [][Next]_vars

====
