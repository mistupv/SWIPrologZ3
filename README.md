# SWIPrologZ3
A simple Prolog API for the Z3 constraint solver

First, you should install SWI Prolog and the Z3 SMT constraint solver.

Once you clone the repository, you can compile the C source file using:
$ swipl-ld -c swiplz3.c
$ swipl-ld -shared -o swiplz3 swiplz3.o -lz3

In order to use the Z3 functions, your Prolog code should load the file swiplz3.pl. For this purpose, you can add 
:- use_module(swiplz3).
to your Prolog file.

Check the simple examples ex1.pl and ex2.pl.
