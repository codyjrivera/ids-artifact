## Supporting artifact for "Predictable Verification using Intrinsic Definitions"
by Anonymous Authors, 2023.

# Dependency Overview
- Boogie 3.0.5
- Z3 4.13.0
- Dafny 4.4.0

# Instructions
1. Make sure you have Z3 installed. A quick way to install Z3, using a Python installation,
   is by `pip install z3-solver`; otherwise, see the [Z3 GitHub](https://github.com/Z3Prover/z3).
2. Make sure you have Boogie installed. Check the 
   [Boogie GitHub](https://github.com/boogie-org/boogie) for more information.
3. Modify the variables `BOOGIE_3` and `PROVER` in
   `./boogie-benchmarks.sh` to point to the location of Boogie and Z3 respectively.
4. To run every benchmark, type `./boogie-all.sh` (you may have to do `chmod +x ./boogie-all.sh`).
   This will take roughly <5 min.
   To run a particular benchmark, type `./boogie-method.sh DATASTRUCTURE METHOD`. For example, to
   run sorted list insert, type `./boogie-method.sh sorted-list insert`.

# Artifact Support for the Paper
The artifact serves primarily to support Table 2 in Section 5 of the paper. The script will print
timing information for each method, combining the time to process the file with Boogie and the
time to run the SMT file. The final number reported in the paper is the sum of the time reported
for each method with the time for verifying the impact sets of each data structure.
