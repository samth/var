RKTS = $(wildcard *.rkt)
OBJS = $(patsubst %.rkt,%,$(RKTS))

testall:
	for x in $(OBJS); do \
	racket -e "(begin (require \"$$x.rkt\") ($$x))"; \
	done

runall:
	for x in `find .  -name '*.rkt'`; do racket $$x; done

