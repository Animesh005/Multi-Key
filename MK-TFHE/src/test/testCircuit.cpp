#include "tfhe.h"
#include "tfhe_io.h"
#include <bits/stdc++.h>
#include <stdio.h>
#include <iostream>
#include <iomanip>
#include <cstdlib>
#include <cmath>
#include <sys/time.h>
#include "polynomials.h"
#include "lwesamples.h"
#include "lwekey.h"
#include "lweparams.h"
#include "tlwe.h"
#include "tgsw.h"



#include "mkTFHEparams.h"
#include "mkTFHEkeys.h"
#include "mkTFHEkeygen.h"
#include "mkTFHEsamples.h"
#include "mkTFHEfunctions.h"


#define WIDTH 5

using namespace std;

void IntSymEncrypt(MKLweSample *res, int p, MKLweKey* MKlwekey)
{
    for (int i = 0; i < WIDTH; i++){
        int bit = p & 1;
        p = (p >> 1);
        MKbootsSymEncrypt(&res[i], bit, MKlwekey);

        // cout << bit << " ";
    }

    // cout << endl;
}

int IntSymDecrypt(MKLweSample *c, MKLweKey* MKlwekey)
{
    int msb = MKbootsSymDecrypt(&c[WIDTH-1], MKlwekey);

    int ans = 0;
    for (int i = 0; i < WIDTH - 1; i++){
        int bit = MKbootsSymDecrypt(&c[i], MKlwekey);
        ans += (bit ^ msb) << i;     // If msb == 1, invert
        cout << bit << " ";
    }
    cout << msb << " ";
    cout << endl;

    if (msb == 1){
        ans++;
        ans = -ans;
    }

    return ans;
}


/** result = result + sample */
void MKlweAddTo(MKLweSample* result, const MKLweSample* sample, const MKTFHEParams* MKparams){
    const int32_t n = MKparams->n;
    const int32_t parties = MKparams->parties;

    for (int i = 0; i < parties; ++i)
    {
        for (int j = 0; j < n; ++j)
        {
            result->a[i*n+j] += sample->a[i*n+j];
        }
    }

    result->b += sample->b;
    result->current_variance += sample->current_variance; 
}

// working .....
void MKbootsMUX(MKLweSample *result, const MKLweSample *a, const MKLweSample *b, const MKLweSample *c,
                     const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, const MKRLweKey *MKrlwekey) {

    static const Torus32 MU = modSwitchToTorus32(1, 8);

    MKLweSample *temp_result = new_MKLweSample(LWEparams, MKparams);
    MKLweSample *temp_result1 = new_MKLweSample(extractedLWEparams, MKparams);
    MKLweSample *u1 = new_MKLweSample(extractedLWEparams, MKparams);
    MKLweSample *u2 = new_MKLweSample(extractedLWEparams, MKparams);


    //compute "AND(a,b)": (0,-1/8) + a + b
    static const Torus32 AndConst = modSwitchToTorus32(-1, 8);
    MKlweNoiselessTrivial(temp_result, AndConst, MKparams);
    MKlweAddTo(temp_result, a, MKparams);
    MKlweAddTo(temp_result, b, MKparams);

    // Bootstrap without KeySwitch
    // MKtfhe_bootstrap_woKSFFT_v2m2(u1, bkFFT, MU, temp_result, RLWEparams, MKparams, MKrlwekey);
    MKtfhe_bootstrapFFT_v2m2(u1, bkFFT, MU, temp_result, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);   
    // MKlweCopy(u1, temp_result, MKparams);
    // cout << "\nu1: " <<  MKbootsSymDecrypt(u1, MKlwekey) << endl;
    // MKlweKeySwitch(u1, bkFFT->ks, temp_result, LWEparams, MKparams);


    //compute "AND(not(a),c)": (0,-1/8) - a + c
    MKlweNoiselessTrivial(temp_result, AndConst, MKparams);
    MKlweSubTo(temp_result, a, MKparams);
    MKlweAddTo(temp_result, c, MKparams);

    // Bootstrap without KeySwitch
    // MKtfhe_bootstrap_woKSFFT_v2m2(u2, bkFFT, MU, temp_result, RLWEparams, MKparams, MKrlwekey);
    MKtfhe_bootstrapFFT_v2m2(u2, bkFFT, MU, temp_result, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);   
    // MKlweCopy(u2, temp_result, MKparams);
    // cout << "\nu2: " <<  MKbootsSymDecrypt(u2, MKlwekey) << endl;
    // MKlweKeySwitch(u2, bkFFT->ks, temp_result, LWEparams, MKparams);

    // Add u1=u1+u2
    static const Torus32 MuxConst = modSwitchToTorus32(1, 8);
    MKlweNoiselessTrivial(temp_result1, MuxConst, MKparams);
    MKlweAddTo(temp_result1, u1, MKparams);
    MKlweAddTo(temp_result1, u2, MKparams);

    // Key switching
    // MKlweKeySwitch(result, bkFFT->ks, temp_result1, LWEparams, MKparams);
    MKtfhe_bootstrapFFT_v2m2(result, bkFFT, MU, temp_result1, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
    // MKlweCopy(result, temp_result1, MKparams);
    // cout << "\ntemp result1: " <<  MKbootsSymDecrypt(temp_result1, MKlwekey) << endl;
    // cout << "\nresult: " <<  MKbootsSymDecrypt(result, MKlwekey) << endl;


    delete_MKLweSample(u2);
    delete_MKLweSample(u1);
    delete_MKLweSample(temp_result1);
    delete_MKLweSample(temp_result);
}


/** result = result + p.sample */
void MKlweAddMulTo(MKLweSample* result, int32_t p, const MKLweSample* sample, const MKTFHEParams* MKparams){
    const int32_t n = MKparams->n;
    const int32_t parties = MKparams->parties;

    for (int i = 0; i < parties; ++i)
    {
        for (int j = 0; j < n; ++j)
        {
            result->a[i*n+j] += p*sample->a[i*n+j];
        }
    }

    result->b += p*sample->b;
    result->current_variance += (p*p)*sample->current_variance; 
}

// working .....
void MKbootsOR(MKLweSample *result, const MKLweSample *ca, const MKLweSample *cb, 
        const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, const MKRLweKey *MKrlwekey) {

    static const Torus32 MU = modSwitchToTorus32(1, 8);

    MKLweSample *temp_result = new_MKLweSample(LWEparams, MKparams);

    //compute: (0,1/8) + ca + cb
    static const Torus32 OrConst = modSwitchToTorus32(1, 8);
    MKlweNoiselessTrivial(temp_result, OrConst, MKparams);
    MKlweAddTo(temp_result, ca, MKparams);
    MKlweAddTo(temp_result, cb, MKparams);

    //if the phase is positive, the result is 1/8
    //if the phase is positive, else the result is -1/8
    MKtfhe_bootstrapFFT_v2m2(result, bkFFT, MU, temp_result, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
    // MKlweCopy(result, temp_result, MKparams);
    

    delete_MKLweSample(temp_result);
}

// working .....
void MKbootsXOR(MKLweSample *result, const MKLweSample *ca, const MKLweSample *cb, 
        const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, const MKRLweKey *MKrlwekey) {

    static const Torus32 MU = modSwitchToTorus32(1, 8);

    MKLweSample *temp_result = new_MKLweSample(LWEparams, MKparams);

    //compute: (0,1/4) + 2*(ca + cb)
    static const Torus32 XorConst = modSwitchToTorus32(1, 4);
    MKlweNoiselessTrivial(temp_result, XorConst, MKparams);
    MKlweAddMulTo(temp_result, 2, ca, MKparams);
    MKlweAddMulTo(temp_result, 2, cb, MKparams);

    //if the phase is positive, the result is 1/8
    //if the phase is positive, else the result is -1/8
    MKtfhe_bootstrapFFT_v2m2(result, bkFFT, MU, temp_result, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
    // MKlweCopy(result, temp_result, MKparams);

    delete_MKLweSample(temp_result);
}

// working .....
void MKbootsAND(MKLweSample *result, const MKLweSample *ca, const MKLweSample *cb, 
        const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, const MKRLweKey *MKrlwekey) {

    static const Torus32 MU = modSwitchToTorus32(1, 8);

    MKLweSample *temp_result = new_MKLweSample(LWEparams, MKparams);

    //compute: (0,-1/8) + ca + cb
    static const Torus32 AndConst = modSwitchToTorus32(-1, 8);
    MKlweNoiselessTrivial(temp_result, AndConst, MKparams);
    MKlweAddTo(temp_result, ca, MKparams);
    MKlweAddTo(temp_result, cb, MKparams);

    //if the phase is positive, the result is 1/8
    //if the phase is positive, else the result is -1/8
    MKtfhe_bootstrapFFT_v2m2(result, bkFFT, MU, temp_result, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
    // MKlweCopy(result, temp_result, MKparams);

    delete_MKLweSample(temp_result);
}


void CktAddWithCarry(const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, const MKRLweKey *MKrlwekey,
            MKLweSample *res, MKLweSample *a, MKLweSample *b, MKLweSample *Cin = NULL)
{
    auto carry = new_MKLweSample(LWEparams, MKparams);
    auto tmp1 = new_MKLweSample(LWEparams, MKparams);
    auto tmp2 = new_MKLweSample(LWEparams, MKparams);
    auto tmp3 = new_MKLweSample(LWEparams, MKparams);

    auto _cin = Cin;

    for (int i = 0; i < WIDTH; i++){

        MKbootsXOR(tmp1, &a[i], &b[i], bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);   // tmp1 = a^b
        MKbootsAND(tmp2, &a[i], &b[i], bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);   // tmp2 = ab
        if (_cin){
            MKbootsXOR(&res[i], tmp1, _cin, bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);  // res = Cin^a^b
            MKbootsAND(tmp3, tmp1, _cin, bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
            MKbootsOR(carry, tmp2, tmp3, bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);    // carry = ab + Cin(a^b)  
        }else{
            MKlweCopy(&res[i], tmp1, MKparams);
            MKlweCopy(carry, tmp2, MKparams);
        }

        _cin = carry;

    }

    MKlweCopy(&res[WIDTH], _cin, MKparams);

    delete_MKLweSample(carry);
    delete_MKLweSample(tmp1);
    delete_MKLweSample(tmp2);
    delete_MKLweSample(tmp3);
}


void CktAdd(const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, const MKRLweKey *MKrlwekey,
            MKLweSample *res, MKLweSample *a, MKLweSample *b, MKLweSample *Cin = NULL)
{
    auto carry = new_MKLweSample(LWEparams, MKparams);
    auto tmp1 = new_MKLweSample(LWEparams, MKparams);
    auto tmp2 = new_MKLweSample(LWEparams, MKparams);
    auto tmp3 = new_MKLweSample(LWEparams, MKparams);

    auto _cin = Cin;

    for (int i = 0; i < WIDTH; i++){

        MKbootsXOR(tmp1, &a[i], &b[i], bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);   // tmp1 = a^b
        MKbootsAND(tmp2, &a[i], &b[i], bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);   // tmp2 = ab
        if (_cin){
            MKbootsXOR(&res[i], tmp1, _cin, bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);  // res = Cin^a^b
            MKbootsAND(tmp3, tmp1, _cin, bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
            MKbootsOR(carry, tmp2, tmp3, bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);    // carry = ab + Cin(a^b)  
        }else{
            MKlweCopy(&res[i], tmp1, MKparams);
            MKlweCopy(carry, tmp2, MKparams);
        }

        _cin = carry;

    }

    delete_MKLweSample(carry);
    delete_MKLweSample(tmp1);
    delete_MKLweSample(tmp2);
    delete_MKLweSample(tmp3);
}


void CktInv(const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, const MKRLweKey *MKrlwekey,
            MKLweSample *res, MKLweSample *a, MKLweSample *one)
{
    for (int i = 0; i < WIDTH; i++){
        MKbootsXOR(&res[i], &a[i], one, bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
    }
}


void CktSub(const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, const MKRLweKey *MKrlwekey,
            MKLweSample *res, MKLweSample *a, MKLweSample *b, MKLweSample *one)
{
    auto tmp = new_MKLweSample_array(WIDTH, LWEparams, MKparams);

    CktInv(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey, tmp, b, one);


    CktAdd(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey, res, a, tmp, one);
    delete_MKLweSample_array(WIDTH, tmp);
   
}


void nBitMul(const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, const MKRLweKey *MKrlwekey,
            MKLweSample *res, MKLweSample *a, MKLweSample *b, MKLweSample *zero, MKLweSample *Cin = NULL)
{
    MKLweSample** BArr = new MKLweSample*[WIDTH];

    auto result = new_MKLweSample_array(2*WIDTH, LWEparams, MKparams);

    for (int i = 0; i < WIDTH; i++) {
        BArr[i] = new_MKLweSample_array(WIDTH, LWEparams, MKparams);
    }

    for (int i=0; i < WIDTH; i++)
    {
        for (int j=0; j < WIDTH; j++)
        {
            MKbootsAND(&BArr[i][j], &a[j], &b[i], bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
        }
    }

    MKlweCopy(&result[0], &BArr[0][0], MKparams);

    auto tmpIn = new_MKLweSample_array(WIDTH, LWEparams, MKparams);

    for (int i=0; i < WIDTH-1; i++)
        MKlweCopy(&tmpIn[i], &BArr[0][i+1], MKparams);

    MKlweCopy(&tmpIn[WIDTH-1], zero, MKparams);

    int ctr=0;

    for (int i=1; i < WIDTH-1; i++)
    {
        auto tmpArr = new_MKLweSample_array(WIDTH+1, LWEparams, MKparams);

        CktAddWithCarry(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey, tmpArr, tmpIn, BArr[i]);

        MKlweCopy(&result[i], &tmpArr[0], MKparams);

        for (int j=0; j < WIDTH; j++)
            MKlweCopy(&tmpIn[j], &tmpArr[j+1], MKparams);

        ctr = i;

    }

    ctr++;

    auto tmpArr = new_MKLweSample_array(WIDTH+1, LWEparams, MKparams);

    CktAddWithCarry(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey, tmpArr, tmpIn, BArr[ctr]);

    for (int i=0; i <= WIDTH; i++)
        MKlweCopy(&result[i+ctr], &tmpArr[i], MKparams);

    // copy WIDTH LSB bits
    for (int i=0; i < WIDTH; i++)
        MKlweCopy(&res[i], &result[i], MKparams);


}


void CktMul(const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, const MKRLweKey *MKrlwekey,
            MKLweSample *res, MKLweSample *a, MKLweSample *b)
{

    auto zero = new_MKLweSample(LWEparams, MKparams);
    auto mres = new_MKLweSample(LWEparams, MKparams);

    MKbootsXOR(mres, &a[WIDTH-1], &b[WIDTH-1], bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);

    MKbootsMUX(&a[WIDTH-1], &a[WIDTH-1], zero, &a[WIDTH-1], bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
    MKbootsMUX(&b[WIDTH-1], &b[WIDTH-1], zero, &b[WIDTH-1], bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);

    nBitMul(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey, res, a, b, zero);

    MKbootsMUX(&res[WIDTH-1], mres, mres, mres, bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);

}



int main()
{

    static const int32_t k = 1;
    static const double ks_stdev = 3.05e-5; // 2.44e-5; //standard deviation
    static const double bk_stdev = 3.29e-10; // 3.72e-9; // 3.29e-10; //standard deviation
    static const double max_stdev = 3.05e-5; //max standard deviation for a 1/4 msg space
    static const int32_t n = 560; //500;            // LWE modulus
    static const int32_t n_extract = 1024;    // LWE extract modulus (used in bootstrapping)
    static const int32_t hLWE = 0;         // HW secret key LWE --> not used
    static const double stdevLWE = max_stdev;      // LWE ciphertexts standard deviation
    static const int32_t Bksbit = 2;       // Base bit key switching
    static const int32_t dks = 8;          // dimension key switching
    static const double stdevKS = ks_stdev; // 2.44e-5;       // KS key standard deviation
    static const int32_t N = 1024;            // RLWE,RGSW modulus
    static const int32_t hRLWE = 0;        // HW secret key RLWE,RGSW --> not used
    static const double stdevRLWEkey = bk_stdev; // 3.29e-10; // 0; // 0.012467;  // RLWE key standard deviation
    static const double stdevRLWE = bk_stdev; // 3.29e-10; // 0; // 0.012467;     // RLWE ciphertexts standard deviation
    static const double stdevRGSW = bk_stdev; // 3.29e-10;     // RGSW ciphertexts standard deviation 
    static const int32_t Bgbit = 9;        // Base bit gadget
    static const int32_t dg = 3;           // dimension gadget
    static const double stdevBK = bk_stdev; // 3.29e-10;       // BK standard deviation
    static const int32_t parties = 2;      // number of parties

    LweParams *extractedLWEparams = new_LweParams(n_extract, ks_stdev, max_stdev);
    LweParams *LWEparams = new_LweParams(n, ks_stdev, max_stdev);
    TLweParams *RLWEparams = new_TLweParams(N, k, bk_stdev, max_stdev);
    MKTFHEParams *MKparams = new_MKTFHEParams(n, n_extract, hLWE, stdevLWE, Bksbit, dks, stdevKS, N, 
                            hRLWE, stdevRLWEkey, stdevRLWE, stdevRGSW, Bgbit, dg, stdevBK, parties);


    cout << "Params: DONE!" << endl;

    // Key generation 
    cout << "Starting KEY GENERATION" << endl;
    clock_t begin_KG = clock();

    // LWE key        
    MKLweKey* MKlwekey = new_MKLweKey(LWEparams, MKparams);
    MKLweKeyGen(MKlwekey);
    cout << "KeyGen MKlwekey: DONE!" << endl;

    // RLWE key 
    MKRLweKey* MKrlwekey = new_MKRLweKey(RLWEparams, MKparams);
    MKRLweKeyGen(MKrlwekey);
    cout << "KeyGen MKrlwekey: DONE!" << endl;

    // LWE key extracted 
    MKLweKey* MKextractedlwekey = new_MKLweKey(extractedLWEparams, MKparams);
    MKtLweExtractKey(MKextractedlwekey, MKrlwekey);
    cout << "KeyGen MKextractedlwekey: DONE!" << endl;

    // bootstrapping + key switching keys
    MKLweBootstrappingKey_v2* MKlweBK = new_MKLweBootstrappingKey_v2(LWEparams, RLWEparams, MKparams);
    MKlweCreateBootstrappingKey_v2(MKlweBK, MKlwekey, MKrlwekey, MKextractedlwekey, 
                                extractedLWEparams, LWEparams, RLWEparams, MKparams);
    cout << "KeyGen MKlweBK: DONE!" << endl;

    // bootstrapping FFT + key switching keys
    MKLweBootstrappingKeyFFT_v2* MKlweBK_FFT = new_MKLweBootstrappingKeyFFT_v2(MKlweBK, LWEparams, RLWEparams, MKparams);
    cout << "KeyGen MKlweBK_FFT: DONE!" << endl;   

    clock_t end_KG = clock();
    double time_KG = ((double) end_KG - begin_KG)/CLOCKS_PER_SEC;
    cout << "Finished KEY GENERATION: " << time_KG << "seconds" << endl;


    int bit1;
    int bit2;

    cout << "Enter the inputs: " << endl;

    for (int i=0; i < 5; i++)
    {
        cin >> bit1 >> bit2;

        cout << bit1 << " " << bit2 << endl;

        auto a = new_MKLweSample_array(WIDTH, LWEparams, MKparams);
        IntSymEncrypt(a, bit1, MKlwekey);

        auto b = new_MKLweSample_array(WIDTH, LWEparams, MKparams);
        IntSymEncrypt(b, bit2, MKlwekey);

        auto res = new_MKLweSample_array(WIDTH, LWEparams, MKparams);
        IntSymEncrypt(res, 0, MKlwekey);

        struct timespec mul_start = {0, 0};
	    struct timespec mul_end = {0, 0};

        clock_gettime(CLOCK_MONOTONIC, &mul_start);
        CktMul(MKlweBK_FFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey, res, a, b);
        clock_gettime(CLOCK_MONOTONIC, &mul_end);

        cout << IntSymDecrypt(res, MKlwekey) << ": Time --> " << (((double)mul_end.tv_nsec + 1.0e+9 * mul_end.tv_sec) - ((double)mul_start.tv_nsec + 1.0e+9 * mul_start.tv_sec)) * 1.0e-9 << " sec" << endl;

    }

    // cout << "Enter the inputs: " << endl;
    // struct timespec gate_start = {0, 0};
	// struct timespec gate_end = {0, 0};

    // int bit1;
    // int bit2;
    // int bit3;
    // int bit4;

    // for (int i=0; i < 6; i++)
    // {
    //     cin >> bit1 >> bit2 >> bit3;

    //     auto a = new_MKLweSample(LWEparams, MKparams);
    //     MKbootsSymEncrypt(a, bit1, MKlwekey);

    //     auto b = new_MKLweSample(LWEparams, MKparams);
    //     MKbootsSymEncrypt(b, bit2, MKlwekey);

    //     auto c = new_MKLweSample(LWEparams, MKparams);
    //     MKbootsSymEncrypt(c, bit3, MKlwekey);

    //     // auto d = new_MKLweSample(LWEparams, MKparams);
    //     // MKbootsSymEncrypt(d, bit4, MKlwekey);

    //     auto res1 = new_MKLweSample(LWEparams, MKparams);
    //     // auto res2 = new_MKLweSample(LWEparams, MKparams);
    //     // auto res3 = new_MKLweSample(LWEparams, MKparams);
    //     // auto res4 = new_MKLweSample(LWEparams, MKparams);

    //     clock_gettime(CLOCK_MONOTONIC, &gate_start);
    //     MKbootsMUX(res1, a, b, c, MKlweBK_FFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey, MKlwekey);
    //     // MKbootsAND(res1, a, b, MKlweBK_FFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
    //     clock_gettime(CLOCK_MONOTONIC, &gate_end);
    //     // cout << "res1: " << MKbootsSymDecrypt(res1, MKlwekey) << endl;
    //     // MKbootsAND(res2, c, d, MKlweBK_FFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
    //     // cout << "res2: " << MKbootsSymDecrypt(res2, MKlwekey) << endl;
    //     // MKbootsAND(res3, res1, res2, MKlweBK_FFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
    //     // cout << "res3: " << MKbootsSymDecrypt(res3, MKlwekey) << endl;
    //     // MKbootsOR(res4, res1, res2, MKlweBK_FFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);

    //     cout << "res4: " << MKbootsSymDecrypt(res1, MKlwekey) << ": Time --> " << (((double)gate_end.tv_nsec + 1.0e+9 * gate_end.tv_sec) - ((double)gate_start.tv_nsec + 1.0e+9 * gate_start.tv_sec)) * 1.0e-9 << " sec" << endl;

    // }


    return 0;
}


