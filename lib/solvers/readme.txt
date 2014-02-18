Adding a new solver:

1. Create a file in this directory.

2. It should contain calls to Zlsolve.register to register modules that
   satisfy the SOLVER interface.

3. Add the file to the SOLVER_OBJS variable in lib/Makefile.

4. Delete the lib/loadsolvers.ml file; it will be rebuilt by make.

