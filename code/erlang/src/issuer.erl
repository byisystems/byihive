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
%%% This module implements the behavior of a Issuer behavior mentioned
%%% in the "Issuer Life Cycle" TLA+ specification.The transition rules
%%% rules can be found in the DOT specification.
%%%
%%% This module is expected to act as one of the participating entity
%%% for the Voucher Issue or Voucher Cancel behavior described in the
%%% TLA+ specification of the same name.
%%%
%%% This module is expected to interact with the VTP module.
%%%
%%% This module uses "ilc" module to keep track of the states of the
%%% Issuer's FSM.
%%% --------------------------------------------------------------------
-module(issuer).

-export([issuer/0]).

-import(logger,[log/1,log/2,log_final_state/2]). % @todo Use a proper logging framework
-import(ilc, [init_fsm/1, init/2, prepare/2, abort/2, issue/2, cancel/2]).

%% ---------------------------------------------------------------------
%% Keeps track of various attributes of the issuer.
%% ---------------------------------------------------------------------
-record(issuer_data, {decision,state,action}).

%% ---------------------------------------------------------------------
%% Initialize the Issuer.
%%
%% If an entity's state is not yet defined, you pass in "initialize" as
%% the state to initialize the entity to the starting state
%%
%% The spawned process can then be used to emulate an Issuer
%% entity whose behavior is defined in the Voucher Issue / Cancel
%% TLA+ specifications.
%% ---------------------------------------------------------------------
issuer() ->
    issuer([], #issuer_data{decision=nil,state=initialize,action=nil}).

%% ---------------------------------------------------------------------
%% The various messages that is received by the Issuer.
%%
%% propose_decision - This is the message sent to the Issuer to initiate
%% them before started to participate in a Voucher Issue / Cancel
%% transaction.
%%
%% query_decision - This is the message sent by the VTP process
%% (VtpPid) to check the current decision state of the Issuer.
%%
%% commit - This is the message sent by the VTP process (VtpPid) which
%% commits the current transaction when both parties in the Voucher
%% Issue / Cancel transaction is in agreement. An acknowledgement is
%% sent back by the Issuer.
%%
%% abort - This is the message sent by the VTP process (VtpPid) which
%% aborts the current transaction either or both the parties in the
%% Voucher Issue / Cancel transaction are not in agreement. An
%% acknowledgement is sent back by the Issuer.
%% ---------------------------------------------------------------------
issuer(Issuers, IssuerData) ->
    receive
        {propose_decision, EntityPid, EntityType, Action, Decision} ->
	    case Action of
		issue ->
		    log("[~p] ~p will take part in: ~p~n", [?MODULE, EntityType, Action]);
		cancel ->
		    log("[~p] ~p will take part in: ~p~n", [?MODULE, EntityType, Action]);
		_ ->
		    log("[~p] !!! ~p cannot take part in ~p. !!!~n", [?MODULE, EntityType, Action]),
		    log("[~p] !!! Voucher transaction has terminated. !!!~n", [?MODULE]),
		    erlang:halt(1)
	    end,
            log("[~p] ~p will propose: ~p~n", [?MODULE, EntityType, Decision]),
	    FsmPid = ilc:init_fsm(IssuerData#issuer_data.state),
	    State = ilc:init(FsmPid, IssuerData#issuer_data.state),
	    log("[~p] ~p has entered the state: ~p~n", [?MODULE, EntityType, State]),
            issuer([EntityPid|Issuers], IssuerData#issuer_data{decision=Decision, state=State, action=Action});
        {query_decision, VtpPid} ->
            log("[~p] Issuer queried by VTP ~p~n", [?MODULE, VtpPid]),
	    State = case IssuerData#issuer_data.decision of
			yes ->
			    FsmPid = ilc:init_fsm(IssuerData#issuer_data.state),
			    ilc:prepare(FsmPid, IssuerData#issuer_data.state);
			no ->
			    IssuerData#issuer_data.state
		    end,
	    UpdatedIssuerData = IssuerData#issuer_data{state=State},
	    log("[~p] issuer has entered the state: ~p~n", [?MODULE, UpdatedIssuerData#issuer_data.state]),
            VtpPid ! {receive_decision, IssuerData#issuer_data.decision, issuer},
            issuer(Issuers, UpdatedIssuerData);
        {commit, VtpPid} ->
	    FsmPid = ilc:init_fsm(IssuerData#issuer_data.state),
	    State = case IssuerData#issuer_data.action of
			issue ->
			    ilc:issue(FsmPid, IssuerData#issuer_data.state);
			cancel ->
			    ilc:cancel(FsmPid, IssuerData#issuer_data.state)
		    end,
	    UpdatedIssuerData = IssuerData#issuer_data{state=State},
	    log("[~p] issuer has entered the state: ~p~n", [?MODULE, UpdatedIssuerData#issuer_data.state]),
            log_final_state(commit, "Issuer"),
            VtpPid ! {acknowledgement};
        {abort, VtpPid} ->
	    FsmPid = ilc:init_fsm(IssuerData#issuer_data.state),
	    State = ilc:abort(FsmPid, IssuerData#issuer_data.state),
	    UpdatedIssuerData = IssuerData#issuer_data{state=State},
	    log("[~p] issuer has entered the state: ~p~n", [?MODULE, UpdatedIssuerData#issuer_data.state]),
            log_final_state(abort, "Issuer"),
            VtpPid ! {acknowledgement}
    end.
