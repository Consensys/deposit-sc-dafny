/*
 * Copyright 2021 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may 
 * not use this file except in compliance with the License. You may obtain 
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT 
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the 
 * License for the specific language governing permissions and limitations 
 * under the License.
 */


include "./DepositSmart.dfy"
include "./helpers/Helpers.dfy"

/**
 *  Example of usage of the DepositSmart class.
 */
module TestDeposit {

    import opened DepositSmart
    import opened Helpers 

    method Main() {

        //  A new contract with f(x,y) = x - y - 1
        var c := new Deposit(3, [0, 0, 0], (x, y) => x - y - 1,0);
        print "Running some tests for the DSC\n";

        c.init_zero_hashes();
        //  zero_hashes = [0, -1, -1]

        var l := [3,6,2,-2,4,5] ; //+ [6];

        // var i := 0;
        // while i < |l| - 1
        //     invariant 0 <= i < |l|
        //     invariant c.count == |l[..i]|
        //     invariant c.count == i 
        //     invariant |l| < power2(c.TREE_HEIGHT) - 1
        //     invariant c.count < power2(c.TREE_HEIGHT) - 1
        // { 
        //     print "=> Depositing: ", l[i], "\n";
        //     c.deposit(l[i]);
        //     print "- Current list is: ", l[.. i + 1], "\n";
        //     var r := c.get_deposit_root();
        //     print "Root Hash for ", l[.. i + 1], " is: ", r, "\n";
        //     i := i + 1;
        // }
       

        var r := c.get_deposit_root();
        print "root for list []: ", r, "\n";
        print "=> Depositing: ", 3, "\n";
        c.deposit(3); 
        r := c.get_deposit_root();
        print "root for list [3]: ", r, "\n";
        print "=> Depositing: ", 6, "\n";
        c.deposit(6); 
        r := c.get_deposit_root();
        print "root for list [3,6]: ", r, "\n";
        print "=> Depositing: ", 2, "\n";
        c.deposit(2); 
        r := c.get_deposit_root();
        print "root for list [3,6,2]:", r, "\n";
        print "=> Depositing: ", -2, "\n";
        c.deposit(-2); 
        r := c.get_deposit_root();
        print "root for list [3,6,2,-2]:", r, "\n";
        print "=> Depositing: ", 4, "\n";
        c.deposit(4); 
        r := c.get_deposit_root();
        print "root for list [3,6,2,-2,4]:", r, "\n";    
        print "=> Depositing: ", 5, "\n";
        c.deposit(5);
        r := c.get_deposit_root();
        print "root for list [3,6,2,-2,4,5]:", r, "\n";

    }
}
