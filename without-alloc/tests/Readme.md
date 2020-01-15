Integration tests, or rather only tests for the allocator.

## Writing tests

Make sure that every test is contained in its own executable file. The reason is
that the test framework itself requires some amount of memory allocation and
this depends on the number of tests ran by each execution. There is only an
option to control the parallelism within an executor, not one to fork for each
test.
