------------------------------- MODULE Atomic -------------------------------
(***************************************************************************)
(* Formal Specification in TLA^+ of the                                    *)
(* Interledger Protocol Atomic (ILP/A)                                     *)
(*                                                                         *)
(* Copyright 2015 Stefan Thomas.                                           *)
(* This work is licensed under the Creative Commons Attribution-4.0        *)
(* International License https://creativecommons.org/licenses/by/4.0/      *)
(*                                                                         *)
(* Modeled after the excellent work by Diego Ongaro:                       *)
(*   Raft - Formal Specification                                           *)
(*   Available at https://github.com/ongardie/raft.tla                     *)
(*   Copyright 2014 Diego Ongaro.                                          *)
(*   This work is licensed under the Creative Commons Attribution-4.0      *)
(*   International License https://creativecommons.org/licenses/by/4.0/    *)
(***************************************************************************)

EXTENDS Naturals, Sequences, TLC

\* The set of ledger IDs
CONSTANTS Ledger

\* Transfer states
CONSTANTS Proposed, Prepared, Executed, Aborted

\* Message types
CONSTANTS ExecuteRequest

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another. TLAPS doesn't support the Bags module, so this is a function
\* mapping Message to Nat.
VARIABLE messages

----
\* The following variables are all per ledger (functions with domain Ledger)

\* The transfer state (Proposed, Prepared, Executed or Aborted)
VARIABLE transferState

\* All ledger variables
ledgerVars == <<transferState>>
----

\* All variables; used for stuttering (asserting state hasn't changed)
vars == <<messages, ledgerVars>>

----
\* Helpers

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] + 1]
    ELSE
        msgs @@ (m :> 1)

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] - 1]
    ELSE
        msgs

\* Add a message to the bag of messages.
Send(m) == messages' = WithMessage(m, messages)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = WithoutMessage(m, messages)

\* Combination of Send and Discard
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))

----
\* Define initial values for all variables

InitLedgerVars == /\ transferState = [i \in Ledger |-> Proposed]

Init == /\ messages = [m \in {} |-> 0]
        /\ InitLedgerVars

----
\* Define state transitions

\* Server i spontaneously executes the transfer - lolwat?
Execute(i) ==
    /\ transferState'          = [transferState EXCEPT ![i] = Executed]
    /\ UNCHANGED <<messages>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives an Execute request from server j
HandleExecuteRequest(i, j, m) ==
    /\ transferState[i] = Proposed
    /\ transferState' = [transferState EXCEPT ![i] = Executed]
    /\ UNCHANGED <<messages>>

\* Receive a message.
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \/ /\ m.mtype = ExecuteRequest
          /\ HandleExecuteRequest(i, j, m)

\* End of message handlers.
----
\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<ledgerVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<ledgerVars>>

----
\* Defines how the variables may transition.

Next == \E i \in Ledger : Execute(i)

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Sat Oct 03 22:20:11 PDT 2015 by moon
\* Created Sat Oct 03 19:18:02 PDT 2015 by moon
