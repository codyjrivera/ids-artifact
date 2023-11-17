## Supporting artifact for "Predictable Verification using Intrinsic Definitions of Data Structures"
by Anonymous Authors, 2023.

# Dependency Overview
- Python 3.10.12
    - sexpdata 1.0.1
- Boogie 3.0.5
- Z3 4.12.2

# Instructions
1. Make sure you have Python 3 installed. To install sexpdata, use `pip install sexpdata`.
2. Make sure you have Z3 installed. A quick way to install Z3 is by `pip install z3-solver`.
3. Make sure you have Boogie installed. Check the 
   [Boogie GitHub](https://github.com/boogie-org/boogie) for more information.
4. Modify the variables `BOOGIE_3`, `PYTHON_3`, and `PROVER` in
   `./boogie-benchmarks.sh` to point to the location
   of Boogie, Python, and Z3 respectively.
5. To run every benchmark, type `./boogie-all.sh` (you may have to do `chmod +x ./boogie-all.sh`).
   To run a particular benchmark, type `./boogie-method.sh DATASTRUCTURE METHOD`. For example, to
   run sorted list insert, type `./boogie-method.sh sorted-list insert`.

# Artifact Support for the Paper
The artifact serves primarily to support Table 2 in Section 5 of the paper. The script will print
timing information for each method, combining the time to process the file with Boogie, the time to 
implant the parametrized updates into the SMT query, and the time to run the SMT file. The final number
reported in the paper is the sum of the time reported for each method with the time for verifying the
impact sets of each datastructure.
