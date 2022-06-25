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

\* The type representing a log item.
\* @typeAlias: LOG_ITEM = [];
LITypeAliases == TRUE

VARIABLES
    \* A bag of records representing requests and responses sent from one server
    \* to another.
    \* @type: MESSAGE -> Int;
    messages

----
\* The following variables are all per server.

VARIABLES
    \* The server's term.
    \* @type: SERVER -> Int;
    currentTerm,

    \* The server's state (Follower, Candidate, or Leader).
    \* @type: SERVER -> STATE;
    state,

    \* The candidate the server voted for in its current term.
    \* If it hasn't voted for any, the value is empty.
    \* @type: SERVER -> Seq(SERVER);
    votedFor

serverVars == <<currentTerm, state, votedFor>>

\* The following variables are used only on candidates:
VARIABLES
    \* The set of servers from which the candidate has received a RequestVote
    \* response in its currentTerm.
    \* @type: SERVER -> Set(SERVER);
    votesResponded,

    \* The set of servers from which the candidate has received a vote in its
    \* currentTerm.
    \* @type: SERVER -> Set(SERVER);
    votesGranted,

    \* A history variable used in the proof. This would not be present in an
    \* implementation.
    \* @type: SERVER -> SERVER -> Seq(LOG_ITEM);
    voterLog

candidateVars == <<votesResponded, votesGranted, voterLog>>

----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, serverVars>>

----
\* Define initial values for all variables

\* @type: Bool;
InitHistoryVars == voterLog = [i \in Server |-> [j \in {} |-> <<>>]]

\* @type: Bool;
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state = [i \in Server |-> Follower]
                  /\ votedFor = [i \in Server |-> <<>>]

\* @type: Bool;
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]

\* @type: Bool;
Init == /\ messages = [m \in {} |-> 0]
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars

----
\* Define state transitions

\* Server i times out and starts a new election.
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = <<>>]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              /\ UNCHANGED messages

----
\* Defines how the variables may transition.
\* @type: Bool;
Next == \E i \in Server : Timeout(i)

\* The specification must start with the initial state and transition according
\* to Next.
\* @type: Bool;
Spec == Init /\ [][Next]_vars

====
