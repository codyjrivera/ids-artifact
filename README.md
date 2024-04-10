# Supporting Artifact for "Predictable Verification using Intrinsic Definitions"
by Anonymous Authors, 2024. Version 3.0 of Artifact.

This is the supporting artifact for "Predictable Verification using Intrinsic Definitions",
by anonymous authors. It contains Boogie and Dafny implementations of a benchmark suite of 
42 data structure manipulating methods over 10 data structures, written in the Fix-What-
You-Break (FWYB) verification paradigm proposed in the paper. It also contains scripts to
verify the benchmarks and record verification times.

## Artifact Outline
We give a rough outline of the artifact's structure:
- `boogie/`: Boogie implementation of the benchmark suite.
- `boogie-builtin/`: Boogie implementation of the benchmark suite, with builtin implementation
   of parametrized map updates used rather than a transplant script, as suggested by a reviewer.
- `dafny/`: Dafny implementation of the benchmark suite.
- `paper/`: A copy of the originally-submitted paper and appendices, for convenience.
- `utils/`: Scripts to generate table data/plots in the paper.
- `dep-locations.sh`: A script file where the user points the script to its dependencies.

## Artifact Setup
There are two ways to set up this artifact. The first way is to use Docker, and the
second way is to set up the evaluation environment manually.

### Docker Setup
The provided `Dockerfile` supplies an Ubuntu 22.04 environment as well as
the recommended versions of the dependencies. Below are instructions for setting up
a container.
1. Install Docker Engine. See [here](https://docs.docker.com/engine/install/) for
   instructions.
2. In the root directory of this artifact, run `docker build -t ids-artifact .` to
   build the container.
3. To obtain an interactive shell for the container `ids-artifact`, run 
   `docker run -it --mount type=bind,src="$(pwd)",target=/outpwd ids-artifact /bin/bash`.
   (the `--mount` option allows you to copy files to the host machine).

Note that `dep-locations.sh` should not have to be modified in this case: the 
`Dockerfile` should have installed all dependencies and placed them in the
user's `PATH`.

### Manual Setup
The artifact requires a Bash shell as well as the following dependencies:
- Python 3 (3.10.12 recommended)
    - sexpdata (1.0.1 recommended)
- Boogie 3.0.1 or later (3.1.2 recommended)
- Z3 (4.13.0 recommended)
- Dafny 4.1.0 or later (4.4.0 recommended)
- GNU time and bc

The artifact has been tested on the recommended versions of the above dependencies. Below
are instructions for installing these dependencies.
1. Make sure you have Python 3 installed. To install sexpdata, an S-expression 
   parser, use `pip install sexpdata`.
2. Install Z3. A quick way, using a Python installation,
   is `pip install z3-solver`; otherwise, see the [Z3 GitHub](https://github.com/Z3Prover/z3).
3. Install Boogie and Dafny. Check out the [Boogie GitHub](https://github.com/boogie-org/boogie)
   and the [Dafny GitHub](https://github.com/dafny-lang/dafny/tree/master) for more information
   on how to install them.
4. Modify `dep-locations.sh` to point to the dependencies. Set the `PYTHON_3`, `BOOGIE_3`, 
   `PROVER`, and `DAFNY_4` variables to the locations of Python, Boogie, Z3, and Dafny
   respectively.

## Artifact Support for Paper Claims
The paper makes the following major claims:

1. We can express a wide range of data structures using intrinsic data structure (IDS)
   definitions, and a wide range of methods mainpulating them using fix-what-you-break
   (FWYB) methodology in Boogie (answer to RQ1).
2. We can effectively verify our Boogie methods using decidable verification condition
   generation and SMT solving (answer to RQ2).
3. Generating decidable verification conditions from programs using FWYB methodology 
   results in better performance than using other automatic verification technologies
   such as Dafny (answer to RQ3).

### Support for Claim 1
Boogie versions of the data structures and methods implemented in Table 2 can be 
seen in the `boogie/` directory of the artifact. Each data structure is contained in 
its own directory, e.g., `single-linked-list/`. The data structure definition, local 
conditions, and FWYB manipulation macros are contained in a file with the same name 
as the directory: e.g., `single-linked-list.bpl`. The impact set proofs 
for each data structure are contained in a file called `impact-sets.bpl`.

Note that there are actually 44 methods defined across the 10 data structures: but two
of them (bst-scaffolding::fix-depth, scheduler-queue::fix-depth) are excluded from 
Table 2 in Section 5 since they contain only ghost code.

We elaborate on the condition that programs be well-behaved (Section 3.4), which is 
required to use FWYB soundly, for one data structure, `single-linked-list`, and one 
method within that data structure, `insert`. We show that the `insert` method is 
well-behaved since it is constructed using carefully-designed macros. Furthermore, we show 
that the impact sets associated with each mutation macro (as described in Section 4.1) 
are correct, by corresponding each mutation
macro with its impact set proof. This is done by extra annotations in the files
`single-linked-list.bpl`, `impact-sets.bpl`, and `insert.bpl` 
(in the directory `boogie/single-linked-list`).

### Support for Claim 2 (~5min)
We have written a script that will verify each of the methods in the `boogie/` 
directory using Boogie as well as a custom script to generate decidable verification 
conditions, sending those verification conditions to an SMT solver. The script will 
also report verification times for all the methods it verifies.

Here is a procedure for running the benchmarks. It assumes you
are in the top-level directory of this artifact.
1. Run `cd boogie`.
2. Run `./boogie-all.sh`.

You can also verify methods individually using `./boogie-method.sh DATASTRUCTURE METHOD`.

These experiments in particular support the `Verif. Time (s)` column on Table 2 in
Section 5 of the paper. The time values on the table for a given method are the sum 
of the time reported by this script for that method, and the time reported by this 
script for the impact set verification of a particular data structure.

A script under the `utils/` directory, `gen-tab2.py`, generates the final time values
for the `Verif. Time (s)` column in Table 2 by performing the above
calculation. To generate these values, complete the following two steps (assuming you 
are in the top-level directory):
1. Run `cd utils`.
2. Run `python3 ./gen-tab2.py RESULTS`, where `RESULTS` is the output from running
   `./boogie-all.sh`.

A sample `RESULTS` is `utils/artifact-boogie-results.txt`.

### Support for Claim 3 (~8hr full, ~2.75hr partial)
We implement our suite of methods using Dafny, a widely used high-level verification
language which does not generate decidable VCs.
The Dafny code implemented for Claim 3 is seen in the `dafny/` directory, and is
structured analogously to how the Boogie code is structured.

We have additionally implemented a script that will verify each of the methods in
`dafny/` using Dafny, as well as provide timings. Here are instructions for
running this script, assuming you are at the top-level directory.
1. Run `cd dafny`.
2. Run `./dafny-all.sh`.

Again, you can verify methods individually using `./dafny-method.sh DATASTRUCTURE METHOD`.

`./dafny-all.sh` excludes the two worst-performing methods: `red-black-tree::insert` and
`scheduler-queue::bst-remove-root`, which take over 2 hours to verify on the experimental
machine used in this paper. To include these benchmarks, either verify them individually, 
or run the `./dafny-all-plus-lt.sh` script.

This experiment, in conjunction with the experiments to support Claim 2, supports the
scatter plot seen near RQ3 in Section 5.3 of the paper, plotting verification times
for Boogie vs. Dafny.

A script under the `utils/` directory, `gen-scrq3.py`, generates the scatter plot
comparing Dafny and Boogie for RQ3. To generate this plot, complete the following 
two steps (assuming you are in the top-level directory):
1. Run `cd utils`.
2. Run `python3 ./gen-scrq3.py DAFNY-RESULTS BOOGIE-RESULTS`, where `DAFNY-RESULTS` is the 
   output from running `./dafny-all.sh`, `BOOGIE-RESULTS` is the output from running
   `./boogie-all.sh`, and `DAFNY-RESULTS` is the output from running `./dafny-all.sh`.
3. Run `cp scatter.png /outpwd` to copy the generated scatter plot to the host machine.
   
A sample `DAFNY-RESULTS` is in `utils/artifact-dafny-results.txt`, while a sample
`BOOGIE-RESULTS` is in `utils/artifact-boogie-results.txt`. Note that the script will
work even with omissions in the Dafny results (e.g., omitting `red-black-tree::insert` and
`scheduler-queue::bst-remove-root` as is done by default).

## Boogie Benchmarks with Builtin Support for Parametrized Updates
In response to a reviewer who pointed out that the transplant script was unnecessary 
since Boogie had builtin support for parametrized updates, we quickly adapted our benchmark
suite to use this support. The suite is located in `boogie-builtin/`. Like the other 
benchmark suites above, one can verify all methods with `./boogie-builtin-all.sh` and 
`./boogie-builitin-method.sh DATASTRUCTURE METHOD`. Verifying all benchmarks takes
~5min, similarly to `boogie/`.
