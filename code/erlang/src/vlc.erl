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
%%% This module implements the State Machine defined in the "Voucher
%%% Life Cycle" TLA+ specification. A diagram of the states and the
%%% transition rules can be found in the DOT specification.
%%%
%%% This Finite State Machine (FSM) is visible to the entities who are
%%% involved in a Voucher operation. In addition to this VTP has
%%% visibility of the current state of the Voucher involved in the
%%% Voucher operaton.
%%%
%%% The FSM exclusively tracks the state of the Voucher. No other
%%% information is tracked or passed here. Given the "current" state,
%%% and the operation being performed, the FSM accurately gives the
%%% the next state.
%%% --------------------------------------------------------------------
-module(vlc).

-export([init_fsm/1, init/2, issue/2, transfer/2, cancel/2, redeem/2]).

-import(logger, [log/1,log/2]). % @todo Use a proper logging framework

%% ---------------------------------------------------------------------
%% Initialize the FSM to a known state for the voucher.
%%
%% If a voucher's does not exist yet, you pass in "initialize" as
%% the state to initialize a phantom voucher, If the voucher does exist
%% then the known state is passed it.
%%
%% The spawned process can then be used to perform transitions in the
%% state machine.
%% ---------------------------------------------------------------------
init_fsm(State) ->
    case State of
	initialize ->
	    spawn(fun() -> initialize() end);
	phantom ->
	    spawn(fun() -> phantom() end);
	valid ->
	    spawn(fun() -> valid() end);
	cancelled  ->
	    spawn(fun() -> cancelled() end);
	redeemed ->
	    spawn(fun() -> redeemed() end);
	_ ->
	    log("[~p] Invalid voucher state (~p) specified~n", [?MODULE, State])
    end.

%% ---------------------------------------------------------------------
%% Valid operations that can be done on a given state of FSM of the
%% Voucher that is defined in the TLA+ and DOT specifications.
%%
%% The variable OpPid is used to refer to the running Pid of the
%% operations.
%% ---------------------------------------------------------------------

%% The function init(), is used when the voucher does not exist.
init(FsmPid, State) ->
    log("[~p] Doing init on voucher in ~p state~n", [?MODULE, State]),
    FsmPid ! {self(), {init, State}},
    receive
	{FsmPid, {init, NextState}} ->
	    NextState
    end.

issue(FsmPid, State) ->
    log("[~p] Doing issue on voucher in ~p state~n", [?MODULE, State]),
    FsmPid ! {self(), {issue, State}},
    receive
	{FsmPid, {issue, NextState}} ->
	    NextState
    end.

transfer(FsmPid, State) ->
    log("[~p] Doing transfer on voucher in ~p state~n", [?MODULE, State]),
    FsmPid ! {self(), {transfer, State}},
    receive
	{FsmPid, {transfer, NextState}} ->
	    NextState
    end.

cancel(FsmPid, State) ->
    log("[~p] Doing cancel on voucher in ~p state~n", [?MODULE, State]),
    FsmPid ! {self(), {cancel, State}},
    receive
	{FsmPid, {cancel, NextState}} ->
	    NextState
    end.

redeem(FsmPid, State) ->
    log("[~p] Doing redeem on voucher in ~p state~n", [?MODULE, State]),
    FsmPid ! {self(), {redeem, State}},
    receive
	{FsmPid, {redeem, NextState}} ->
	    NextState
    end.

%% ---------------------------------------------------------------------
%% Valid states for a Voucher that is defined in the TLA+ and
%% DOT specifications.
%%
%% The variable FsmPid is used to refer to the running Pid of the
%% current state.
%%
%% This is private to the module and is not exposed.
%% ---------------------------------------------------------------------

%% The function initialize(), is used when the Voucher does not exist.
initialize() ->
    receive
	{OpPid, {init, State}} ->
	    NextState = phantom,
	    OpPid ! {self(), {init, NextState}},
	    log("[~p] Initialized voucher from ~p to ~p~n", [?MODULE, State, NextState]);
	_ ->
	    log("[~p] Invalid operation on initializing voucher~n", [?MODULE])
    end.

phantom() ->
    receive
        {OpPid, {issue, State}} ->
	    NextState = valid,
	    OpPid ! {self(), {issue, NextState}},
	    log("[~p] State of voucher set from ~p to ~p~n", [?MODULE, State, NextState]);
        _ ->
            log("[~p] Invalid operation on phantom voucher~n", [?MODULE])
    end.

valid() ->
    receive
        {OpPid, {transfer, State}} ->
	    NextState = valid,
	    OpPid ! {self(), {transfer, NextState}},
	    log("[~p] State of voucher set from ~p to ~p~n", [?MODULE, State, NextState]);
	{OpPid, {cancel, State}} ->
	    NextState = cancelled,
	    OpPid ! {self(), {cancel, NextState}},
	    log("[~p] State of voucher set from ~p to ~p~n", [?MODULE, State, NextState]);
	{OpPid, {redeem, State}} ->
	    NextState = redeemed,
	    OpPid ! {self(), {redeem, NextState}},
	    log("[~p] State of voucher set from ~p to ~p~n", [?MODULE, State, NextState]);
        _ ->
            log("[~p] Invalid operation on valid state of voucher~n", [?MODULE])
    end.

cancelled() ->
    receive
        _ ->
            log("[~p] Invalid operation on cancelled state of voucher~n", [?MODULE])
    end.

redeemed() ->
    receive
        _ ->
            log("[~p] Invalid operation on redeemed state of voucher~n", [?MODULE])
    end.
