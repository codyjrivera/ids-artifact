## Supporting Artifact for "Predictable Verification using Intrinsic Definitions"
by Anonymous Authors, 2023.

This is the supporting artifact for "Predictable Verification using Intrinsic Definitions",
by anonymous authors. It contains Boogie and Dafny implementations of a benchmark suite of 
42 data structure manipulating methods over 10 data structures, written in the Fix-What-
You-Break (FWYB) verification paradigm proposed in the paper. It also contains scripts to
verify the benchmarks and record verification times.

# Artifact Outline
We give an outline of the artifact's structure:
- `boogie/`: Boogie implementation of the benchmark suite.
- `dafny/`: Dafny implementaiton of the benchmark suite.
- `paper/`: A copy of the originally-submitted paper and appendices, for convenience.
- `boogie-*.sh`: Scripts for running the Boogie benchmark suite.
- `dafny-*.sh`: Scripts for running the Dafny benchmark suite.

# Overview of the Benchmarks
An implementation of the benchmark suite in Boogie and Dafny can be seen in the `boogie/`
and `dafny/` subdirectories respectively. Each data structure is contained in its own
directory, e.g., `single-linked-list/`. The data structure definition, local conditions,
and FWYB manipulation macros are contained in a file with the same name as the directory:
e.g., `single-linked-list.(bpl|dfy)` (Boogie or Dafny respectively). The impact set proofs 
for each data structure are contained in a file called `impact-sets.(bpl|dfy)`.

Note: there are actually 44 methods defined across the 10 data structures: but two
of them (bst-scaffolding::fix-depth, scheduler-queue::fix-depth) are excluded from Table 2 in Section
5 since they contain only ghost code.

# Artifact Setup
The artifact requires a Bash shell environment as well as the following dependencies:
- Boogie 3.0.1 or later (3.1.2 recommended)
- Z3 (4.13.0 recommended)
- Dafny 4.1.0 or later (4.4.0 recommended)

The artifact has been tested on the recommended versions of the above dependencies. Below
are instructions for installing these dependencies.
1. Install Z3. A quick way, using a Python installation,
   is `pip install z3-solver`; otherwise, see the [Z3 GitHub](https://github.com/Z3Prover/z3).
2. Install Boogie and Dafny. Check out the [Boogie GitHub](https://github.com/boogie-org/boogie)
   and the [Dafny GitHub](https://github.com/dafny-lang/dafny/tree/master) for more information
   on how to install them.
3. Modify `dep-locations.sh` to point to the dependencies. Set the `BOOGIE_3`, `PROVER`, and
   `DAFNY_4` variables to the locations of Boogie, Z3, and Dafny respectively.

# Running the Boogie Benchmarks
To run the entire Boogie benchmark suite, run the script `./boogie-all.sh`. To run an individual
benchmark from the Boogie benchmark suite, run the script `./boogie-method.sh DATASTRUCTURE METHOD`,
where `DATASTRUCTURE` is the desired data structure, and `METHOD` is the desired method.

These benchmarks are primarily designed to support RQ1 and RQ2 in Section 5. More specifically,
the resulting verification times support the "Verif. Time(s)" column in Table 2 of the paper.
The reported verification time for a method is taken to be the sum of the time to verify the method 
and the time to verify its data structure's impact set.

Note: there is no longer a script which augments SMT files with parametrized map update implementations as
described in the paper, since a reviewer pointed out that Boogie had built-in support for parametrized
map updates.

# Running the Dafny Benchmarks
To run the entire Dafny benchmark suite, run the script `./dafny-all.sh`. This excludes two methods
for which we have experienced very long (>2 hour) verification times: `red-black-tree::insert` and
`scheduler-queue::bst-remove-root`. To run the benchmark suite with all methods including those two,
run the script `dafny-all-plus-lt.sh`.

To run an individual benchmark from the Dafny benchmark suite, run the script 
`./dafny-method.sh DATASTRUCTURE METHOD`, where `DATASTRUCTURE` is the desired data structure,
and `METHOD` is the desired method.

These benchmarks are primarily designed to support RQ3 in Section 5. The verification times for the
Dafny benchmarks, in combination with the verification times for the Boogie benchmarks, combine to
support the scatter plot that appears alongside RQ3.
