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
%%% This module helps execute the Voucher Transaction System. This of
%%% this as the equivalent of a "supervisor" for the code base.
%%%
%%% The module acts as a user interface to interact with the VTS and
%%% checkout how various transactions work out.
%%% --------------------------------------------------------------------
-module(test_driver).
-export([start/0,start/1]).

-import(vtp,[vtp/0]).
-import(holder_receive,[holder_receive/0]).
-import(holder_transmit,[holder_transmit/0]).
-import(collector,[collector/0]).
-import(issuer,[issuer/0]).
-import(logger,[log/1,log/2]).
-import(vdb, [generate/1,getv/1,putv/1]).

start() ->
    log("Following tests are available:~n"),
    log("test_commit - Shows a simple commit (issue).~n"),
    log("test_abort - Shows an abort (during cancel).~n"),
    log("test_redeem - Shows a redeem operation.~n"),
    log("test_transfer - Shows a transfer operation.~n"),
    log("test_exception - Shows an exception when an invalid voucher is used.~n"),
    log("=========~n"),
    log("To run a test, do the following~n"),
    log("test_driver:start(<name>)~n").

start(TestName) ->
    case TestName of
	test_commit ->
	    spawn(fun() -> test_commit() end);
	test_abort ->
	    spawn(fun() -> test_abort() end);
	test_redeem ->
	    spawn(fun() -> test_redeem() end);
	test_transfer ->
	    spawn(fun() -> test_transfer() end);
	test_exception ->
	    spawn(fun() -> test_exception() end);
	test_voucher_db ->
	    spawn(fun() -> test_voucher_db() end);
	_ ->
	    log("Invalid option selected~n")
    end.

test_commit() ->
    VTP = spawn(vtp, vtp, []),
    H = spawn(holder_receive, holder_receive, []),
    I = spawn(issuer, issuer, []),
    V = spawn(voucher, voucher, []),

    VTP ! {add_entity, H, holder},
    VTP ! {add_entity, I, issuer},
    VTP ! {add_voucher, V},

    Voucher = vdb:generate(I),
    H ! {propose_decision, H, holder, issue, yes},
    I ! {propose_decision, I, issuer, issue, yes},
    V ! {prepare_voucher, issue, I, H, Voucher},

    log("=== Voucher transaction has started. ===~n", []),

    VTP ! {vtp_start, self()},

    receive
	{vtp_end} ->
	    log("=== Voucher transaction has finished. ===~n", [])
    end.

test_abort() ->
    VTP = spawn(vtp, vtp, []),
    H = spawn(holder_receive, holder_receive, []),
    I = spawn(issuer, issuer, []),
    V = spawn(voucher, voucher, []),

    VTP ! {add_entity, H, holder},
    VTP ! {add_entity, I, issuer},
    VTP ! {add_voucher, V},

    Voucher = vdb:getv(502),
    H ! {propose_decision, H, holder, cancel, no},
    I ! {propose_decision, I, issuer, cancel, yes},
    V ! {prepare_voucher, cancel, I, H, Voucher},

    log("=== Voucher transaction has started. ===~n", []),

    VTP ! {vtp_start, self()},

    receive
	{vtp_end} ->
	    log("=== Voucher transaction has finished. ===~n", [])
    end.

test_redeem() ->
    VTP = spawn(vtp, vtp, []),
    H = spawn(holder_transmit, holder_transmit, []),
    C = spawn(collector, collector, []),
    V = spawn(voucher, voucher, []),

    VTP ! {add_entity, H, holder},
    VTP ! {add_entity, C, collector},
    VTP ! {add_voucher, V},

    Voucher = vdb:getv(502),
    H ! {propose_decision, H, holder, redeem, yes},
    C ! {propose_decision, C, collector, redeem, yes},
    V ! {prepare_voucher, redeem, H, C, Voucher},

    log("=== Voucher transaction has started. ===~n", []),

    VTP ! {vtp_start, self()},

    receive
	{vtp_end} ->
	    log("=== Voucher transaction has finished. ===~n", [])
    end.

test_transfer() ->
    VTP = spawn(vtp, vtp, []),
    HT = spawn(holder_transmit, holder_transmit, []),
    HR = spawn(holder_receive, holder_receive, []),
    V = spawn(voucher, voucher, []),

    VTP ! {add_entity, HT, holder},
    VTP ! {add_entity, HR, holder},
    VTP ! {add_voucher, V},

    Voucher = vdb:getv(501),
    HT ! {propose_decision, HT, holder, transfer, yes},
    HR ! {propose_decision, HR, holder, transfer, yes},
    V  ! {prepare_voucher, transfer, HT, HR, Voucher},

    log("=== Voucher transaction has started. ===~n", []),

    VTP ! {vtp_start, self()},

    receive
	{vtp_end} ->
	    log("=== Voucher transaction has finished. ===~n", [])
    end.

test_exception() ->
    VTP = spawn(vtp, vtp, []),
    H = spawn(holder_receive, holder_receive, []),
    I = spawn(issuer, issuer, []),
    V = spawn(voucher, voucher, []),

    VTP ! {add_entity, H, holder},
    VTP ! {add_entity, I, issuer},
    VTP ! {add_voucher, V},

    % Try to issue a valid voucher
    Voucher = vdb:getv(501),
    H ! {propose_decision, H, holder, issue, yes},
    I ! {propose_decision, I, issuer, issue, yes},
    V ! {prepare_voucher, issue, I, H, Voucher},

    log("=== Voucher transaction has started. ===~n", []),

    VTP ! {vtp_start, self()},

    receive
	{vtp_end} ->
	    log("=== Voucher transaction has finished. ===~n", [])
    end.

test_voucher_db() ->
    I = spawn(issuer, issuer, []),

    log("~p is the VoucherData", [vdb:generate(I)]),
    log("~p is the VoucherData", [vdb:getv(501)]).
