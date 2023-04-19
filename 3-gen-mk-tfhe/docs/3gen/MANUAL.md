# MK-TFHE Repo Explanations

---
14th December 2022, Yavuz AKIN 


## General Structure

__/src:__ contains the source code used to run MK-TFHE.

__/measurements:__ contains the code to run statistical tests and their results.

__multikey.jl:__ code to run an example using the CCS MK-TFHE.

__multikey\_new.jl:__ code to run an example using the KMS MK-TFHE.

__multikey\_new\_fast.jl:__ code to run an example using the fast variant of the KMS MK-TFHE.

__multikey\_3gen.jl:__ code to run an example using the our variant of MK-TFHE.

__Others:__ not important or should be supressed.


## Modifications made to the source files

### 3gen\_mk\_gates.jl

Contains the implementation of the NAND gate using the 3rd generation scheme.

### 3gen\_mk\_internals.jl

This File contains structures and functions to perform Bootstrapping for the 3rd generation of MK-TFHE.

* __new BootstrapKeyPart_3gen struct :__ This new struct is needed to add bootstrapping key generated with common public keys. It contains different constructors according to the method used.

* The struct of MKBootstrapKey is not used like in previous implementations.

* Other functions implemented in this file are pretty forward.

### api.jl

* __new Schemeparameters_3gen struct :__ It's basically the same as Schemeparameters but I created it anyway in case modifications needed to be made for the 3gen (lwe\_noise\_stddev and ks\_noise\_stddev are the same).

* Parameter conversion functions such as lwe\_parameters, tgsw\_parameters have also been added.

* __new SecretKey_3gen struct :__ Same as SecretKey.

* The struct of CloudKey is not used in 3gen since the naming is confusing and it is not really needed.

### mk\_api.jl

* The new parameter sets for 3gen have been added.

* Instead of having a function that generates a SharedKey, __GenCRP_3gen__ has been implemented that generates a __CRP_3gen__ (see mk.internals.jl) which is a less confusing term for a common random polynomial. Actually it contains d common random polynomials. The user can choose if those d polynomials are the same or different using the a_same variable (by default they are not the same, this can be changed later on).

* The structure of CloudKeyPart is not used in 3gen. For test purposes a constructor not using FFT for multiplication has been implemented but this is for CCS. The new constructor can be erased later.

* The structure of MKCloudKey is not used in 3gen.

* __mk\_encrypt\_gen:__ same as mk\_encrypt.
* __mk\_decrypt\_3gen:__ same mk\_decrypt.


### mk_internals.jl

This file is the most confusing one. It contains code that is used by all three schemes. The structure of the code forces us to put some of the new code of 3gen here.

* new __CRP\_3gen__ struct : structure that stores the common random polynomial. Actually it stores d common random polynomials to take into account the initial design where we have an unique randomness and many CRPs. If the simplified design with one CRP and many randomness is used, the a_same variable must be put to true. (Later if we don't want the initial version anymore we can change this code).

* new constructor for __PublicKey__ : A new constructor is added to take as argument CRP\_3gen instead of SharedKey. In addition all constructors have been added a wo\_FFT version that can be removed later.

* new struct __CommonPubKey\_3gen__ : struct that contains the common public key obtaind by summing all the individuals public keys.

* __mk\_keyswitch\_3gen__ : The keyswitch function used in 3gen is a bit different than the original one because we switch from a ciphertext of size 2 to a ciphertext of size \#parties. The optimal keyswitch that was described in CCS could also be implemented.

* __mk\_tgsw\_encrypt\_wo\_FFT__: uni-encryption without using FFT for the generation of bootstrapping keys without FFT for CCS and KMS.


### numeric-functions.jl

* New random generators have been added, for the generation of keys with coefficients in [-1,0,1] with non uniform distribution.
* __noise_calc__ : new function to calculate the noise of the phase accroding to the expected value.

### tgsw_3gen.jl

This file contains the code that implements the multiparty TGSW sample that we have introduced in the initial version and in the simplified version.

* __tgsw\_encrypt\_3gen__ : MK-TGSW sample encrypted with the Common public key

* __tgsw\_extern\_mul\_3gen__ : External multiplication between RLweSample and TGswSample\_3gen.


## Measurements 

The measurements folder contains two folder :

* test_suites : contains all the code for the measurements.
* test_results : contains the results of the measurements.

### test_suites

The test suites are divided into schemes : CCS, KMS, us_simplified (one CRP).

Each scheme has the same type of tests.

* __measurements\_\<scheme\>\_3.jl__ : In this experiment we want to analyze the noise after bootstrapping and the wrong decryptions related to bootstrapping of bootstrapped samples. Two fresh encryptions are bootstrapped, their noise is measured. Then, they are given as input to a NAND gate and rounded. The total number of wrong decryptions is measured. The wrong decryptions may originate because of two reasons.
	* the added phase of 1/8 - c1 - c2 is such that their total phase after rounding is < 0 so the bootstrapping bootstraps correctly but to the wrong value.

	* Boostrapping leads to wrong decryption eventhough the phase of 1/8 - c1 - c2 is correct (same as fresh bootstrapping error).

	P.S. There is also one other case that is measured : when the phase 1/8 - c1 - c2 > 1/4. The bootstrapping doesn't lead to wrong decryption but this can be wrong if we were not in boolean field. The number of this situation happening is also counted.

	So, there are two cases in which there is wrong decryption. One situation is not measured. When both cases occur at the same time, this can lead to correct decryption. But this is a really rare scenario.
	
	In addition to these, we also measure minimum and median bootstrap time per parameter set,precomp time per parameter set (although I'm not sure this one is useful), BK and KSK sizes.
	
Then, the us_simplified scheme one more test that compares its result while using FFT and without using FFT during precomputation.

* __measurements\_us\_simplified\_4.jl__ : The bootstrapping of fresh samples is computed and their noises are measured using precomputation with FFT for all parameter sets for the 3gen scheme. The results can then be compared between with and without FFT.


Finally, one last test is performed in the /performance_comparison_test folder using all schemes.

* __perf\_comp.jl__ : For each scheme, we take the parameter set for 16 party, we compute the bootstrapping of fresh samples and measure the time of bootstrapping for comparison purposes. this is done with 2,4,8,16 parties (but still with 16 parameter set).

### test_results

The results of the test\_suites are test_results. The results are divided by scheme.

__/logs__ : contains the logs of the measurements (debugging, precise indications on the errors occuring, ...).

__mk\_bk\_sizes\_\<scheme\_number\>.dat__ : contains the mean size of a bootstrapping key per parameter set.

__mk\_ksk\_sizes\_\<scheme\_number\>.dat__ : contains the mean size of a key switching key per parameter set.

__mk\_bootstrap\_min\_time\_\<scheme\_number\>.dat__ : contains the min time required to run the bootstrapping gate per parameter set.

__mk\_bootstrap\_median\_time\_\<scheme\_number\>.dat__ : contains the median time required to run the bootstrapping gate per parameter set.  

__precomp\_times.dat__ : precomputation times per parameter set if there is any. (I don't think this is really helpful).

__mk-noises\_\_scheme-\<n\>\_parties-\<k\>\_lambda-100\_pi-2\_qw-2\_sf-4.00.dat__ : contains the noise values after execution of bootstrapping (with fresh encryptions) for the scheme number n executed with k parties with the paramset\_number-th parameter set.

__mk-noises\_\_scheme-\<n\>\_parties-\<k\>\_lambda-100\_pi-2\_qw-2\_sf-4.00\_w\_FFT.dat__ : Same as previous but with precomp done using FFT.

__mk-negative\_errors\_\<scheme\_number\>.dat__ : The number of wrong decryptions related the added phase of 1/8 - c1 - c2 after rounding being lower than 0 leading to wrong decryption although bootstrapping is correct. The results are per parameter set.

__mk-negative\_errors\_\<scheme\_number\>.dat__ : The count of decryptions that are correct but where phase of 1/8 - c1 - c2 after rounding is higher than 1/4. The results are per parameter set.  






















