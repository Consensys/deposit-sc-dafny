
[ [up] ](../README.md) 

# How to check the proofs?

To mechanically check the proofs you can either use our Docker container with Dafny pre-installed, or install Dafny on your computer.
To check the proofs we recommend the latest Dafny release 3.0.0 (the analysis should work with Dafny 2.3.0 but execution times may differ.)

> Most of the files can be verified using the VSCode plugin running Dafny.
> However, for a few more complex proofs, the plugin default configuration
> is unlikely to complete the analysis. In the sequel we provide a script 
> to run the verification of all the files (without timeouts.)
## Using a Docker container

Pre-requisites:

1. a working installation of [Docker](https://docs.docker.com),
2. a fork or clone of this repository.

A simple way to check the proofs is to use a pre-configured installation of Dafny 3.0.0  with a Docker container.

On Unix-based system, `cd` to the root directory of your working copy of this repository.
```bash
/home/user1/ $ git clone git@github.com:ConsenSys/deposit-sc-dafny.git
/home/user1/ $ cd deposit-sc-dafny
/home/user1/deposit-sc-dafny $ 
```

The next commands will start a Docker container with [Linux, Dotnet and Dafny 3.0.0](https://hub.docker.com/repository/docker/franck44/linux-dafny) (pre-installed), and mount your local working directory as a volume in the Docker machine (this way you can access it from the running Docker machine).
You can check that your system is correctly set up with the following commands:
```bash
/home/user1/deposit-sc-dafny $ docker run -v /home/user1/deposit-sc-dafny:/deposit-sc-dafny -it franck44/linux-dafny /bin/bash
root@749938cb155d:/# dafny /version
Dafny 3.0.0.30203
root@749938cb155d:/# cd deposit-sc-dafny/
root@749938cb155d:/deposit-sc-dafny# dafny /dafnyVerify:1 /compile:0 src/dafny/smart/helpers/Helpers.dfy 
Dafny program verifier finished with 9 verified, 0 errors
root@749938cb155d:/deposit-sc-dafny# 
```

You can collect more information about the verification using Dafny command line arguments:
```bash
root@749938cb155d:/deposit-sc-dafny# dafny /dafnyVerify:1 /compile:0 /noCheating:1 /trace /traceTimes /tracePOs src/dafny/smart/helpers/Helpers.dfy 
Parsing src/dafny/smart/helpers/Helpers.dfy
>>> Starting resolution   [-4.9E-05 s]
>>> Starting resolution   [0.181145 s]
>>> Starting typechecking   [0.191269 s]
Coalescing blocks...
Inlining...
>>> Starting abstract interpretation   [0.380332 s]

Running abstract interpretation...
  [0.044256 s]
>>> Starting implementation verification   [0.431046 s]
>>> Starting live variable analysis   [0.45118 s]
[TRACE] Using prover: /Users/franck/local/dafny3.0.0/z3/bin/z3
>>> Finished implementation verification   [0.780033 s]

Verifying CheckWellformed$$Helpers.__default.power2 ...
  [0.349 s, 12 proof obligations]  verified
>>> Starting implementation verification   [0.78408 s]
>>> Starting live variable analysis   [0.784191 s]
>>> Finished implementation verification   [0.861801 s]

Verifying CheckWellformed$$Helpers.__default.power2Lemmas ...
  [0.078 s, 2 proof obligations]  verified
>>> Starting implementation verification   [0.861961 s]
>>> Starting live variable analysis   [0.862099 s]
>>> Finished implementation verification   [0.936414 s]

Verifying Impl$$Helpers.__default.power2Lemmas ...
  [0.075 s, 4 proof obligations]  verified
>>> Starting implementation verification   [0.936657 s]
>>> Starting live variable analysis   [0.936744 s]
>>> Finished implementation verification   [1.008124 s]

Verifying CheckWellformed$$Helpers.__default.power2Div2 ...
  [0.072 s, 2 proof obligations]  verified
>>> Starting implementation verification   [1.008376 s]
>>> Starting live variable analysis   [1.008525 s]
>>> Finished implementation verification   [1.082494 s]

Verifying Impl$$Helpers.__default.power2Div2 ...
  [0.074 s, 2 proof obligations]  verified
>>> Starting implementation verification   [1.08283 s]
>>> Starting live variable analysis   [1.083055 s]
>>> Finished implementation verification   [1.154731 s]

Verifying CheckWellformed$$Helpers.__default.power2Div2LessThan ...
  [0.072 s, 2 proof obligations]  verified
>>> Starting implementation verification   [1.154986 s]
>>> Starting live variable analysis   [1.155082 s]
>>> Finished implementation verification   [1.228862 s]

Verifying Impl$$Helpers.__default.power2Div2LessThan ...
  [0.074 s, 2 proof obligations]  verified
>>> Starting implementation verification   [1.229152 s]
>>> Starting live variable analysis   [1.229297 s]
>>> Finished implementation verification   [1.300845 s]

Verifying CheckWellformed$$Helpers.__default.power2LessThanDiv2 ...
  [0.072 s, 3 proof obligations]  verified
>>> Starting implementation verification   [1.301053 s]
>>> Starting live variable analysis   [1.301264 s]
>>> Finished implementation verification   [1.375682 s]

Verifying Impl$$Helpers.__default.power2LessThanDiv2 ...
  [0.075 s, 2 proof obligations]  verified

Dafny program verifier finished with 9 verified, 0 errors
root@749938cb155d:/deposit-sc-dafny# 
```

An example of a an object creation and usage is provided in 
[RunDeposit.dy](https://github.com/ConsenSys/deposit-sc-dafny/blob/master/src/dafny/smart/RunDeposit.dfy) and be executed in the docker container by:

```bash
root@749938cb155d:/deposit-sc-dafny# dafny  /compile:4  src/dafny/smart/RunDeposit.dfy
Dafny program verifier finished with 1 verified, 0 errors
Running...

Running some tests for the DSC
root for list []: -1
=> Depositing: 3
root for list [3]: 2
=> Depositing: 6
root for list [3,6]: -4
=> Depositing: 2
root for list [3,6,2]:-6
=> Depositing: -2
root for list [3,6,2,-2]:-8
=> Depositing: 4
root for list [3,6,2,-2,4]:-12
=> Depositing: 5
root for list [3,6,2,-2,4,5]:-7
root@749938cb155d:/deposit-sc-dafny#
```

Finally you can check all the files using the following command (it can take up to several minutes to process all the files):
```bash
root@749938cb155d:/deposit-sc-dafny# ./verifyAllOpt.sh src/dafny/smart
```
This script will run Dafny (`noCheating` mode on) with some tracing options that provide some statistics on the verification.

> On a MacBook Pro 2.3 GHz 8-Core Intel Core i9, running Docker 3.0.0, the previous analysis
> (of all the files) takes around 4mins, and you should see the progress on the standard output.  


## Install Dafny on your computer

Pre-requisites:

* install Dafny, see [our Dafny wiki](./dafny-install.md).
* clone or fork this repository.

Assuming you have a running Dafny compiler, you may use the following command line to check a `*.dfy` file:
```bash
> dafny /dafnyVerify:1 /compile:0  src/dafny/smart/helpers/Helpers.dfy 

Dafny program verifier finished with 9 verified, 0 errors
```

You can check all the files using the following command:
```bash
> ./verifyAllOpt.sh src/dafny/smart
```
