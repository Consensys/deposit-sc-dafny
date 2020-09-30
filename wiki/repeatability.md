
[ [up] ](../README.md) 

# How to check the proofs?

To mechanically check the proofs you can either our Docker container with Dafny pre-installed, or istall Dafny on your computer.
To check the proofs we recommend Dafny 2.3.0 (we have not tested the most recent pre-release 3.0.x). 

## Using a Docker container

Pre-requisites:

1. a working installation of [Docker](https://docs.docker.com),
2. a fork or clone of this repository.

A simple way to check the proofs is to use a pre-configured installation of Dafny on a Docker container.

On Unix-based system, `cd` to the root directory of your working copy of this repository.
```bash
/home/user1/ $ git clone git@github.com:PegaSysEng/deposit-sc-dafny.git
/home/user1/ $ cd deposit-sc-dafny
/home/user1/deposit-sc-dafny $ 
```

The next commands will start a [Docker container](https://hub.docker.com/repository/docker/franck44/linux-dafny) with Dafny pre-installed, and mount your local working directory as a volume in the Docker machine (this way you can access it from the running Docker machine).
You can check that your system is correctly set up with the following commands:
```bash
/home/user1/deposit-sc-dafny $ docker run -v /home/user1/deposit-sc-dafny:/deposit-sc-dafny -it franck44/linux-dafny /bin/bash
root@749938cb155d:/# cd deposit-sc-dafny/
root@749938cb155d:/deposit-sc-dafny# dafny /dafnyVerify:1 /compile:0 src/dafny/smart/helpers/Helpers.dfy 
Dafny 2.3.0.10506

Dafny program verifier finished with 9 verified, 0 errors
root@749938cb155d:/deposit-sc-dafny# 
```
You can check all the files using the following command (it can take up to several minutes all the files):
```bash
/home/user1/deposit-sc-dafny $ ./verifyAllRec.sh src/dafny/smart
```
This script will run Dafny wth some tracing options that provide some statistics on the verification.

## Install Dafny on your computer

Pre-requisites:

* install Dafny, see [our Dafny wiki](./dafny-install.md).
* clone or fork this repository.

Assuming you have a running Dafny compiler, you may use the following command line to check a `*.dfy` file:
```bash
> dafny /dafnyVerify:1 /compile:0  src/dafny/smart/helpers/Helpers.dfy 
Dafny 2.3.0.10506

Dafny program verifier finished with 9 verified, 0 errors
```

You can check all the files using the following command:
```bash
> ./verifyAllRec.sh src/dafny/smart
```
