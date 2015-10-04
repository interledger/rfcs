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

EXTENDS Naturals, Sequences, Bags, TLC

\* The set of ledger IDs
CONSTANTS Ledger

\* The set of participant IDs
CONSTANTS Participant

\* Transfer states
CONSTANTS Proposed, Prepared, Executed, Aborted

\* Message types
CONSTANTS PrepareRequest, ExecuteRequest, PrepareNotify, ExecuteNotify

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another.
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
Send(m) == messages' = messages (+) SetToBag({m})

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = messages (-) SetToBag({m})

\* Combination of Send and Discard
Reply(response, request) ==
    messages' = messages (-) SetToBag({request}) (+) SetToBag({response})

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----
\* Define initial values for all variables

InitLedgerVars == /\ transferState = [i \in Ledger |-> Proposed]

Init == /\ messages = EmptyBag
        /\ InitLedgerVars

----
\* Define state transitions

\* A participant i asks a ledger j to prepare a transfer
Prepare(i, j) ==
    /\ Send([mtype   |-> PrepareRequest,
             msource |-> i,
             mdest   |-> j])
    /\ UNCHANGED <<ledgerVars>>

\* Server i spontaneously requests somebody should execute the transfer - lolwat?
Execute(i, j) ==
    /\ Send([mtype   |-> ExecuteRequest,
             msource |-> i,
             mdest   |-> j])
    /\ UNCHANGED <<ledgerVars>>

\* Participant i starts off the chain
Start(i) ==
    /\ Prepare(i, i+1)

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a Prepare request from participant j
HandlePrepareRequest(i, j, m) ==
    LET valid == /\ transferState[i] = Proposed
                 /\ j = i - 1
    IN \/ /\ valid
          /\ transferState' = [transferState EXCEPT ![i] = Prepared]
          /\ Reply([mtype   |-> PrepareNotify,
                    msource |-> i,
                    mdest   |-> i+1], m)
       \/ /\ \lnot valid
          /\ Discard(m)
          /\ UNCHANGED <<ledgerVars>>

\* Server i receives an Execute request from server j
HandleExecuteRequest(i, j, m) ==
    LET valid == /\ transferState[i] = Prepared
    IN \/ /\ valid
          /\ transferState' = [transferState EXCEPT ![i] = Executed]
          /\ Reply([mtype   |-> ExecuteNotify,
                    msource |-> i,
                    mdest   |-> i-1], m)
       \/ /\ \lnot valid
          /\ Discard(m)
          /\ UNCHANGED <<ledgerVars>>

\* Ledger j notifies participant i that the transfer is prepared
HandlePrepareNotify(i, j, m) ==
    LET isRecipient == i = Max(Participant)
    IN \/ /\ isRecipient
          /\ Reply([mtype   |-> ExecuteRequest,
                    msource |-> i,
                    mdest   |-> i-1], m)
          /\ UNCHANGED <<ledgerVars>>
       \/ /\ \lnot isRecipient
          /\ Reply([mtype   |-> PrepareRequest,
                    msource |-> i,
                    mdest   |-> i+1], m)
          /\ UNCHANGED <<ledgerVars>>

\* Ledger j notifies participant i that the transfer is executed
HandleExecuteNotify(i, j, m) ==
    LET isSender == i = Min(Participant)
    IN \/ /\ \lnot isSender
          /\ Reply([mtype   |-> ExecuteRequest,
                    msource |-> i,
                    mdest   |-> i-1], m)
          /\ UNCHANGED <<ledgerVars>>
       \/ /\ isSender
          /\ Discard(m)
          /\ UNCHANGED <<ledgerVars>>

\* Receive a message.
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \/ /\ m.mtype = PrepareRequest
          /\ HandlePrepareRequest(i, j, m)
       \/ /\ m.mtype = ExecuteRequest
          /\ HandleExecuteRequest(i, j, m)
       \/ /\ m.mtype = PrepareNotify
          /\ HandlePrepareNotify(i, j, m)
       \/ /\ m.mtype = ExecuteNotify
          /\ HandleExecuteNotify(i, j, m)

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

Next == \/ Start(Min(Participant))
        \/ \E m \in DOMAIN messages : Receive(m)

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

=============================================================================
