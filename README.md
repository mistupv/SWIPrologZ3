# SWIPrologZ3

### A simple SWI Prolog API for Microsoft's SMT solver Z3 


First, you should install SWI Prolog and the SMT solver Z3. It has been tested with SWI Prolog version 7.6.3 and Z3 version 4.6.1.

Then, you can download or clone the repository, e.g., 

````$ git clone https://github.com/mistupv/SWIPrologZ3.git````

and compile the C source file using the SWI Prolog utility program ````swipl-ld````, as follows:

````$ swipl-ld -c swiplz3.c````

````$ swipl-ld -shared -o swiplz3 swiplz3.o -lz3````

Now, in order to use the Z3 functions, your Prolog code should load the file ```swiplz3.pl```. For this purpose, you can add

````:- use_module(swiplz3).````

to your Prolog file.

Check the simple examples ```ex1.pl``` and ```ex2.pl```.

This is ongoing work. Currently, it only covers constraints over integers and a few basic Z3 functions.

Please send me any comment to <gvidal@dsic.upv.es>
