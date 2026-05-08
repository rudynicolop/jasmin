# Tests of the Rocq printer

This directory contains the test suite of Rocq printer for Jasmin.
checker.

Run it with `dune runtest` (see documentation of dune for details).

If the output of some test changes, use `dune promote` to update the
`*.expected` files that contain the expected output. (If the change is not
expected, fix the test or the checker instead.)
