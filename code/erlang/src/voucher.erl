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
%%% This module implements the behavior of a Voucher behavior mentioned
%%% in the "Voucher Life Cycle" TLA+ specification.The transition rules
%%% rules can be found in the DOT specification.
%%%
%%% This module is expected to act as one of the participating entity
%%% for the Voucher Operations (Issue / Redeem / Transfer Cancel)
%%% behavior described in the TLA+ specification of the same name.
%%%
%%% This module is expected to interact with the VTP module.
%%%
%%% This module uses "vlc" module to keep track of the states of the
%%% Voucher's FSM.
%%% --------------------------------------------------------------------
-module(voucher).

-export([voucher/0]).

-import(logger,[log/1,log/2,log_final_state/2]). % @todo Use a proper logging framework
-import(vlc, [init_fsm/1, init/2, issue/2, transfer/2, cancel/2, redeem/2]).

%% ---------------------------------------------------------------------
%% Keeps track of various attributes of the voucher.
%% ---------------------------------------------------------------------
-record(voucher_data, {id, state, origin, owner}).
-record(voucher_txn_data, {transmit_pid, receive_pid, action, voucher_data}).

%% ---------------------------------------------------------------------
%% Initialize the Voucher.
%%
%% A voucher is initialized with null voucher_data, this is because this
%% module acts as a "handler" for the vouchers which the entities wish
%% to interact with.
%%
%% The voucher is added into the module through a message after
%% initialization.
%%
%% The spawned process can then be used to emulate an Voucher
%% entity whose behavior is defined in the Voucher Operations TLA+
%% specifications.
%% ---------------------------------------------------------------------
voucher() ->
    voucher([], #voucher_txn_data{transmit_pid=nil,receive_pid=nil,
				  action=nil, voucher_data=#voucher_data{}}).

%% ---------------------------------------------------------------------
%% The various messages that is received by the Voucher.
%%
%% prepare_voucher - This is the message sent to initialize them voucher
%% handler. This is where the source and destination Pids indicated  by
%% TransmitPid and ReceivePid respectively. A voucher's state (unlike
%% an entity) can be either existing (valid or redeemed for example) or
%% non-existing (like phantom for example), in either case we need to
%% make sure that the state of the voucher is "restored" correct
%% for both existing and non-existing vouchers.
%%
%% commit - This is the message sent by the VTP process (VtpPid) which
%% commits the current transaction when both parties in the Voucher
%% transaction is in agreement. This causes the voucher handler to
%% set the correct state of the voucher after the voucher operation.
%% An acknowledgement is sent back by the Voucher handler.
%%
%% abort - This is the message sent by the VTP process (VtpPid) which
%% aborts the current transaction either or both the parties in the
%% Voucher ransaction are not in agreement. No state changes are made
%% to the voucher. An acknowledgement is sent back by the Voucher.
%% ---------------------------------------------------------------------
voucher(Vouchers, VoucherTxnData) ->
    receive
        {prepare_voucher, Action, TransmitPid, ReceivePid, VoucherData} ->
            log("[~p] ~p is the transmit entity~n", [?MODULE, TransmitPid]),
            log("[~p] ~p is the receive entity~n", [?MODULE, ReceivePid]),
	    VoucherState = VoucherData#voucher_data.state,
	    try is_valid_voucher(Action, VoucherState) of
		true ->
		    log("[~p] ~p on voucher with state \"~p\" is legal.~n", [?MODULE, Action, VoucherState])
	    catch
		_:false ->
		    log("[~p] !!! ~p on voucher with state '~p' is illegal. !!!~n", [?MODULE, Action, VoucherState]),
		    log("[~p] !!! Voucher transaction has terminated. !!!~n", [?MODULE]),
		    erlang:halt(1)
	    end,
	    FsmPid = vlc:init_fsm(VoucherState),
	    log("[~p] ~p is action taken on the voucher~n", [?MODULE, Action]),
	    State = case Action of
			issue ->
			    vlc:init(FsmPid, VoucherState);
			_ ->
			  VoucherState
		    end,
	    UpdatedVoucherData = VoucherData#voucher_data{state=State},
	    log("[~p] Voucher (~p) has entered the state: ~p~n", [?MODULE, VoucherData, State]),
	    UpdatedVoucherTxnData = VoucherTxnData#voucher_txn_data{
				      transmit_pid=TransmitPid,
				      receive_pid=ReceivePid,
				      action=Action,
				      voucher_data=UpdatedVoucherData
				     },
            voucher([VoucherData|Vouchers], UpdatedVoucherTxnData);
        {commit, VtpPid} ->
	    VoucherData = VoucherTxnData#voucher_txn_data.voucher_data,
	    FsmPid = vlc:init_fsm(VoucherData#voucher_data.state),
	    State = case VoucherTxnData#voucher_txn_data.action of
			issue ->
			    vlc:issue(FsmPid, VoucherData#voucher_data.state);
			transfer ->
			    vlc:transfer(FsmPid, VoucherData#voucher_data.state);
			redeem ->
			    vlc:redeem(FsmPid, VoucherData#voucher_data.state);
			cancel ->
			    vlc:cancel(FsmPid, VoucherData#voucher_data.state)
		    end,
	    UpdatedVoucherData = VoucherData#voucher_data{state=State},
	    log("[~p] voucher has entered the state: ~p~n", [?MODULE, UpdatedVoucherData#voucher_data.state]),
            log_final_state(commit,"Voucher"),
            VtpPid ! {acknowledgement};
        {abort, VtpPid} ->
	    VoucherData = VoucherTxnData#voucher_txn_data.voucher_data,
	    log("[~p] voucher has entered the state: ~p~n", [?MODULE, VoucherData#voucher_data.state]),
            log_final_state(abort,"Voucher"),
            VtpPid ! {acknowledgement}
    end.

%% ---------------------------------------------------------------------
%% Validates a voucher making sure that the given "action" and the
%% "state" of Voucher combination is valid for conducting a voucher
%% transaction.
%% ---------------------------------------------------------------------
is_valid_voucher(Action, VoucherState) ->
    case Action of
	issue when VoucherState == initialize ->
	    true;
	redeem when VoucherState == valid ->
	    true;
	cancel when VoucherState == valid ->
	    true;
	transfer when VoucherState == valid ->
	    true;
	_Else ->
	    throw(false)
    end.
