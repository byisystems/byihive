## --------------------------------------------------------------------
## Copyright (c) 2018, Backyard Innovations Pte. Ltd., Singapore.
##
## Released under the terms of the Apache License 2.0
## See: file LICENSE in root directory for details.
##
## This file contains Intellectual Property that belongs to
## Backyard Innovations Pte Ltd., Singapore.
##
## Author: Santhosh Raju    <santhosh@byisystems.com>
## --------------------------------------------------------------------
DOT=dot
SIZE=9,15\!
DPI=100
IMG=png

.PHONY: all
all: voucherlifecycle

voucherlifecycle:
	$(DOT) -Gsize=$(SIZE) -Gdpi=$(DPI) -T$(IMG) VoucherLifeCycle.gv \
	-o VoucherLifeCycle.png

.PHONY: clean
clean:
	rm -f *.png
