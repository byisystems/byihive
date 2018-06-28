## --------------------------------------------------------------------
## Copyright (c) 2018, Backyard Innovations Pte. Ltd., Singapore.
##
## Released under the terms of the Apache License 2.0
## See: file LICENSE that came with this software for details.
##
## This file contains Intellectual Property that belongs to
## Backyard Innovations Pte Ltd., Singapore.
##
## Author: Santhosh Raju    <santhosh@byisystems.com>
## --------------------------------------------------------------------
MSCGEN=mscgen
IMG=png

.PHONY: all
all:	voucherissue    \
	vouchercancel   \
	voucherredeem   \
	vouchertransfer

voucherissue:
	$(MSCGEN) -T $(IMG) -i VoucherIssue.msc -o VoucherIssue.png

vouchercancel:
	$(MSCGEN) -T $(IMG) -i VoucherCancel.msc -o VoucherCancel.png

voucherredeem:
	$(MSCGEN) -T $(IMG) -i VoucherRedeem.msc -o VoucherRedeem.png

vouchertransfer:
	$(MSCGEN) -T $(IMG) -i VoucherTransfer.msc -o VoucherTransfer.png

.PHONY: clean
clean:
	rm -f *.png
