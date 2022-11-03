#
# Makefile for hpspresso
#
PROG=hpspresso
LDADD=-lmbin1 -lm
PREFIX?=/usr/local
MAN=
SRCS=hpspresso.c
BINDIR?=${PREFIX}/bin

.if defined(HAVE_STATIC)
LDFLAGS+= -static
.endif

.if defined(HAVE_DEBUG)
CFLAGS+= -g -O0
.endif

.include <bsd.prog.mk>
