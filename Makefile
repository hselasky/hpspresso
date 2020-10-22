PROG=hpspresso
LDADD=-lmbin1
MAN=
SRCS=hpspresso.c
BINDIR?=/usr/local/bin
CFLAGS+= -static

.if defined(HAVE_DEBUG)
CFLAGS+= -g -O0
.endif

.include <bsd.prog.mk>
