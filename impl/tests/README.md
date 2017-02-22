# File system test scripts

A collection of tests for file system implementations with an automated test script. Run all tests using `./run_tests.sh <fstype1> <fstype2>`. This compares the implementation of `fstype1` with `fstype2`; a test fails when checksums produced by the tests do not match across the two file system implementations.

The `scripts` folder contains all test scripts. `common` contains non-test scripts used by multiple tests. 

Additional tests should be added into the `scripts` folder, and follow the template provided in `test_template.sh`.
