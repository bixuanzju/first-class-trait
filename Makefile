
build:
	@stack build

install:
	@stack install

test:
	@stack test

clean:
	@stack clean

coq:
	@make -C coq

.PHONY: all build test run clean doc install
