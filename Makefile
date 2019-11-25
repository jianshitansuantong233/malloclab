#
# Makefile for the Malloc Lab
#
HANDINDIR = /u/cs/class/cs33/cs33t3/cs33-malloclab/grade/handin

CC = gcc
CFLAGS = -Wall -O3 -g

OBJS = mdriver.o mm.o memlib.o fsecs.o fcyc.o clock.o ftimer.o

mdriver: $(OBJS)
	$(CC) $(CFLAGS) -o mdriver $(OBJS)

mdriver.o: mdriver.c fsecs.h fcyc.h clock.h memlib.h config.h mm.h
memlib.o: memlib.c memlib.h
mm.o: mm.c mm.h memlib.h
fsecs.o: fsecs.c fsecs.h config.h
fcyc.o: fcyc.c fcyc.h
ftimer.o: ftimer.c ftimer.h config.h
clock.o: clock.c clock.h

handin:
	@USER=whoami
	cp mm.c $(HANDINDIR)/$(USER)-mm.c

clean:
	rm -f *~ *.o mdriver


