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
