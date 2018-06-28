%%% --------------------------------------------------------------------
%%% @copyright 2018, Backyard Innovations Pte. Ltd., Singapore.
%%%
%%% Released under the terms of the GNU Affero General Public License
%%% v3.0. See: file LICENSE that came with this software for details.
%%%
%%% This file contains Intellectual Property that belongs to
%%% Backyard Innovations Pte Ltd., Singapore.
%%%
%%% @author Santhosh Raju <santhosh@byisystems.com>
%%% @author Cherry G. Mathew <cherry@byisystems.com>
%%% --------------------------------------------------------------------

%%% --------------------------------------------------------------------
%%% This module implements the State Machine defined in the "Issuer
%%% Life Cycle" TLA+ specification. A diagram of the states and the
%%% transition rules can be found in the DOT specification.
%%%
%%% This Finite State Machine (FSM) is private to the entity who is
%%% involved in a Voucher operation. So the VTP has no visibility of the
%%% the current state of the Entity involved in the Voucher operaton.
%%%
%%% The FSM exclusively tracks the state of the Entity. No other
%%% information is tracked or passed here. Given the "current" state,
%%% and the operation being performed, the FSM accurately gives the
%%% the next state.
%%% --------------------------------------------------------------------
-module(ilc).

-export([init_fsm/1, init/2, prepare/2, abort/2, issue/2, cancel/2]).

-import(logger,[log/1,log/2,log_final_state/2]). % @todo Use a proper logging framework

%% ---------------------------------------------------------------------
%% Initialize the FSM to a known state for the entity.
%%
%% If an entity's state is not yet defined, you pass in "initialize" as
%% the state to initialize the entity to the starting state
%%
%% The spawned process can then be used to perform transitions in the
%% state machine.
%% ---------------------------------------------------------------------
init_fsm(State) ->
    case State of
	initialize ->
	    spawn(fun() -> initialize() end);
	waiting ->
	    spawn(fun() -> waiting() end);
	prepared ->
	    spawn(fun() -> prepared() end);
	issued  ->
	    spawn(fun() -> issued() end);
	cancelled  ->
	    spawn(fun() -> cancelled() end);
	aborted ->
	    spawn(fun() -> aborted() end);
	_ ->
	    log("[~p] Invalid issuer state (~p)  specified~n", [?MODULE, State])
    end.

%% ---------------------------------------------------------------------
%% Valid operations that can be done on a given state of FSM of the
%% Issuer that is defined in the TLA+ and DOT specifications.
%%
%% The variable OpPid is used to refer to the running Pid of the
%% operations.
%% ---------------------------------------------------------------------

%% The function init(), is used when the entity is undefined.
init(FsmPid, State) ->
    log("[~p] Doing init on issuer in ~p state~n", [?MODULE, State]),
    FsmPid ! {self(), {init, State}},
    receive
	{FsmPid, {init, NextState}} ->
	    NextState
    end.

prepare(FsmPid, State) ->
    log("[~p] Doing prepare on issuer in ~p state~n", [?MODULE, State]),
    FsmPid ! {self(), {prepare, State}},
    receive
	{FsmPid, {prepare, NextState}} ->
	    NextState
    end.

abort(FsmPid, State) ->
    log("[~p] Doing abort on issuer in ~p state~n", [?MODULE, State]),
    FsmPid ! {self(), {abort, State}},
    receive
	{FsmPid, {abort, NextState}} ->
	    NextState
    end.

issue(FsmPid, State) ->
    log("[~p] Doing issue on issuer in ~p state~n", [?MODULE, State]),
    FsmPid ! {self(), {issue, State}},
    receive
	{FsmPid, {issue, NextState}} ->
	    NextState
    end.

cancel(FsmPid, State) ->
    log("[~p] Doing cancel on issuer in ~p state~n", [?MODULE, State]),
    FsmPid ! {self(), {cancel, State}},
    receive
	{FsmPid, {cancel, NextState}} ->
	    NextState
    end.

%% ---------------------------------------------------------------------
%% Valid states for a Issuer that is defined in the TLA+ and
%% DOT specifications.
%%
%% The variable FsmPid is used to refer to the running Pid of the
%% current state.
%%
%% This is private to the module and is not exposed.
%% ---------------------------------------------------------------------

%% The function initialize(), is used when the entity is undefined.
initialize() ->
    receive
	{OpPid, {init, State}} ->
	    NextState = waiting,
	    OpPid ! {self(), {init, NextState}},
	    log("[~p] Initialized issuer from ~p to ~p~n", [?MODULE, State, NextState]);
	_ ->
	    log("[~p] Invalid operation on initializing issuer~n", [?MODULE])
    end.

waiting() ->
    receive
        {OpPid, {prepare, State}} ->
	    NextState = prepared,
	    OpPid ! {self(), {prepare, NextState}},
	    log("[~p] State of issuer set from ~p to ~p~n", [?MODULE, State, NextState]);
        {OpPid, {abort, State}} ->
	    NextState = aborted,
	    OpPid ! {self(), {abort, NextState}},
	    log("[~p] State of issuer set from ~p to ~p~n", [?MODULE, State, NextState]);
        _ ->
            log("[~p] Invalid operation on waiting state of issuer~n", [?MODULE])
    end.

prepared() ->
    receive
        {OpPid, {issue, State}} ->
	    NextState = issued,
	    OpPid ! {self(), {issue, NextState}},
	    log("[~p] State of issuer set from ~p to ~p~n", [?MODULE, State, NextState]);
        {OpPid, {cancel, State}} ->
	    NextState = cancelled,
	    OpPid ! {self(), {cancel, NextState}},
	    log("[~p] State of issuer set from ~p to ~p~n", [?MODULE, State, NextState]);
        {OpPid, {abort, State}} ->
	    NextState = aborted,
	    OpPid ! {self(), {abort, NextState}},
	    log("[~p] State of issuer set from ~p to ~p~n", [?MODULE, State, NextState]);
        _ ->
            log("[~p] Invalid operation on prepared state of issuer~n", [?MODULE])
    end.

cancelled() ->
    receive
        _ ->
            log("[~p] Invalid operation on cancelled state of issuer~n", [?MODULE])
    end.

issued() ->
    receive
        _ ->
            log("[~p] Invalid operation on issued state of issuer~n", [?MODULE])
    end.

aborted() ->
    receive
        _ ->
            log("[~p] Invalid operation on aborted state of issuer~n", [?MODULE])
    end.
