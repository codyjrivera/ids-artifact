# Supporting Artifact for
# "Predictable Verification using Intrinsic Definitions"
# by Anonymous Authors.
# 
# Artifact by Anonymous Author, 2024. 
#
# Dockerfile for artifact.

FROM ubuntu:22.04

WORKDIR /scratch

# Environment variables to avoid interactive stuff.
ARG DEBIAN_FRONTEND=noninteractive
ENV TZ=Etc/UTC

# Install base dependencies.
RUN apt-get update
RUN apt-get -y upgrade
RUN apt-get install -y time bc wget unzip python3 python3-pip python-is-python3

# Install sexpdata.
RUN pip install sexpdata

# Install Boogie (3.1.3).
RUN apt-get install -y dotnet6
RUN dotnet tool install --global Boogie --version 3.1.3
ENV PATH="$PATH:/root/.dotnet/tools"

# Install z3 (4.13.0).
RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.13.0/z3-4.13.0-x64-glibc-2.35.zip
RUN unzip z3-4.13.0-x64-glibc-2.35.zip
ENV PATH="$PATH:/scratch/z3-4.13.0-x64-glibc-2.35/bin"

# Install Dafny (4.4.0).
RUN wget https://github.com/dafny-lang/dafny/releases/download/v4.4.0/dafny-4.4.0-x64-ubuntu-20.04.zip
RUN unzip dafny-4.4.0-x64-ubuntu-20.04.zip
ENV PATH="$PATH:/scratch/dafny"

# Establish benchmark directory.
WORKDIR /ids-artifact
COPY . .
