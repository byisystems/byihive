Erlang
======

This is a barebones implementation of how a Voucher Trading System (VTS) should function based on the original RFC3506 and the TLA+ specifications that we built around it.

How to build
------------

Information on building and installing [Erlang/OTP](http://www.erlang.org) can
be found [here](https://github.com/erlang/otp/wiki/Installation) ([more
info](https://github.com/erlang/otp/blob/master/HOWTO/INSTALL.md)).

Once you have Erlang/OTP installed doing a `make` should build the application.

Running the Erlang code
-----------------------

Once build is complete, you can run the script `test_driver.sh` which will be found in the `ebin/` folder.

When this script is run, you will be presented with the EShell, where you get to choose the various tasks that can be performed within the EShell.

So if you wanted to run an example "Transfer" operation you would run.

`> test_driver:start(test_transfer).`

Once you hit the `Return` key, you should be able to see a textual log of the various events in the transaction.

License
-------

GNU Affero General Public License v3.0. See LICENSE.