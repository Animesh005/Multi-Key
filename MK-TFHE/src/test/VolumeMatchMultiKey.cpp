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


#define WIDTH 8

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
        // cout << bit << " ";
    }
    // cout << msb << " ";
    // cout << endl;

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


    //compute "AND(not(a),c)": (0,-1/8) - a + c
    MKlweNoiselessTrivial(temp_result, AndConst, MKparams);
    MKlweSubTo(temp_result, a, MKparams);
    MKlweAddTo(temp_result, c, MKparams);

    // Bootstrap without KeySwitch
    // MKtfhe_bootstrap_woKSFFT_v2m2(u2, bkFFT, MU, temp_result, RLWEparams, MKparams, MKrlwekey);
    MKtfhe_bootstrapFFT_v2m2(u2, bkFFT, MU, temp_result, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);   

    // Add u1=u1+u2
    static const Torus32 MuxConst = modSwitchToTorus32(1, 8);
    MKlweNoiselessTrivial(temp_result1, MuxConst, MKparams);
    MKlweAddTo(temp_result1, u1, MKparams);
    MKlweAddTo(temp_result1, u2, MKparams);

    // Key switching
    // MKlweKeySwitch(result, bkFFT->ks, temp_result1, LWEparams, MKparams);
    MKtfhe_bootstrapFFT_v2m2(result, bkFFT, MU, temp_result1, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);


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

    delete_MKLweSample(temp_result);
}


// working .....
void CktAdd(const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, const MKRLweKey *MKrlwekey,
            MKLweSample *res, MKLweSample *a, MKLweSample *b, MKLweSample *Cin = NULL)
{
    auto carry = new_MKLweSample(LWEparams, MKparams);
    auto tmp1 = new_MKLweSample(LWEparams, MKparams);
    auto tmp2 = new_MKLweSample(LWEparams, MKparams);
    auto tmp3 = new_MKLweSample(LWEparams, MKparams);

    // auto tmp_res = new_MKLweSample_array(WIDTH, LWEparams, MKparams);

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

    // static const Torus32 MU = modSwitchToTorus32(1, 8);

    // for (int i=0; i < WIDTH; i++){
    //     MKtfhe_bootstrapFFT_v2m2(&res[i], bkFFT, MU, &tmp_res[i], LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
    // }

    delete_MKLweSample(carry);
    delete_MKLweSample(tmp1);
    delete_MKLweSample(tmp2);
    delete_MKLweSample(tmp3);
    // delete_MKLweSample_array(WIDTH, tmp_res);
}


// working .....
void CktInv(const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, MKLweKey *MKlwekey, const MKRLweKey *MKrlwekey,
            MKLweSample *res, MKLweSample *a, MKLweSample *one)
{
    for (int i = 0; i < WIDTH; i++){
        MKbootsXOR(&res[i], &a[i], one, bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
    }
}


// working .....
void CktSub(const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, MKLweKey* MKlwekey, const MKRLweKey *MKrlwekey,
            MKLweSample *res, MKLweSample *a, MKLweSample *b, MKLweSample *one)
{
    auto tmp = new_MKLweSample_array(WIDTH, LWEparams, MKparams);

    CktInv(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKlwekey, MKrlwekey, tmp, b, one);

    // static const Torus32 MU = modSwitchToTorus32(1, 8);
    // MKLweSample *temp_result = new_MKLweSample_array(WIDTH, LWEparams, MKparams);
    // for (int i = 0; i < WIDTH; i++){
    //     MKtfhe_bootstrapFFT_v2m2(&temp_result[i], bkFFT, MU, &tmp[i], LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
    // }

    CktAdd(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey, res, a, tmp, one);
    delete_MKLweSample_array(WIDTH, tmp);
    // delete_MKLweSample_array(WIDTH, temp_result);
}


// working .....
void CktLess(const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, MKLweKey *MKlwekey, const MKRLweKey *MKrlwekey,
            MKLweSample *res, MKLweSample *a, MKLweSample *b, MKLweSample *one)     // res = (a < b)
{
    auto tmp = new_MKLweSample_array(WIDTH, LWEparams, MKparams);

    CktSub(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKlwekey, MKrlwekey, tmp, a, b, one);

    // static const Torus32 MU = modSwitchToTorus32(1, 8);
    // MKLweSample *temp_result = new_MKLweSample_array(WIDTH, LWEparams, MKparams);
    // for (int i = 0; i < WIDTH; i++){
    //     MKtfhe_bootstrapFFT_v2m2(&temp_result[i], bkFFT, MU, &tmp[i], LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
    // }

    MKlweCopy(res, &tmp[WIDTH-1], MKparams);
    delete_MKLweSample_array(WIDTH, tmp);
    // delete_MKLweSample_array(WIDTH, temp_result);
}


// working .....
void CktGrt(const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, MKLweKey *MKlwekey, const MKRLweKey *MKrlwekey,
            MKLweSample *res, MKLweSample *a, MKLweSample *b, MKLweSample *one)     // res = (a > b)
{
    auto tmp = new_MKLweSample_array(WIDTH, LWEparams, MKparams);

    CktSub(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKlwekey, MKrlwekey, tmp, b, a, one);

    // static const Torus32 MU = modSwitchToTorus32(1, 8);
    // MKLweSample *temp_result = new_MKLweSample_array(WIDTH, LWEparams, MKparams);
    // for (int i = 0; i < WIDTH; i++){
    //     MKtfhe_bootstrapFFT_v2m2(&temp_result[i], bkFFT, MU, &tmp[i], LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
    // }

    MKlweCopy(res, &tmp[WIDTH-1], MKparams);
    delete_MKLweSample_array(WIDTH, tmp);
    // delete_MKLweSample_array(WIDTH, temp_result);
}


// working .....
void CktGeq(const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, MKLweKey *MKlwekey, const MKRLweKey *MKrlwekey,
            MKLweSample *res, MKLweSample *a, MKLweSample *b, MKLweSample *one)     // res = (a >= b)
{
    auto tmp = new_MKLweSample(LWEparams, MKparams);
    CktLess(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKlwekey, MKrlwekey, tmp, a, b, one);
    MKbootsXOR(res, tmp, one, bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
    delete_MKLweSample(tmp);
}

// working .....
void CktLeq(const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, MKLweKey *MKlwekey, const MKRLweKey *MKrlwekey,
            MKLweSample *res, MKLweSample *a, MKLweSample *b, MKLweSample *one)     // res = (a <= b)
{
    auto tmp = new_MKLweSample(LWEparams, MKparams);
    CktGrt(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKlwekey, MKrlwekey, tmp, a, b, one);
    MKbootsXOR(res, tmp, one, bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
    delete_MKLweSample(tmp);
}

// working .....
void CktEq(const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, MKLweKey *MKlwekey, const MKRLweKey *MKrlwekey,
            MKLweSample *res, MKLweSample *a, MKLweSample *b, MKLweSample *one)     // res = (a == b)
{
    auto grt = new_MKLweSample(LWEparams, MKparams);
    auto lss = new_MKLweSample(LWEparams, MKparams);

    CktGrt(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKlwekey, MKrlwekey, grt, a, b, one);
    CktLess(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKlwekey, MKrlwekey, lss, a, b, one);

    auto gol = new_MKLweSample(LWEparams, MKparams);
    MKbootsOR(gol, grt, lss, bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
    MKbootsXOR(res, gol, one, bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);

    delete_MKLweSample(grt);
    delete_MKLweSample(lss);
    delete_MKLweSample(gol);
}

// Buy and Sell order ints should not be longer than WIDTH bits.
struct Orders
{
    vector<int> buy;
    vector<int> sell;
};

struct EncOrders
{
    vector<MKLweSample *> buy;
    vector<MKLweSample *> sell;
};

void VolumeMatch(EncOrders *ord, EncOrders *resOrd,
                 MKLweSample *accBuy, MKLweSample *accSell,
                 MKLweSample *accTmp1, MKLweSample *accTmp2,
                 const MKLweBootstrappingKeyFFT_v2 *bkFFT, const LweParams* LWEparams, const LweParams *extractedLWEparams, 
        const TLweParams* RLWEparams, const MKTFHEParams *MKparams, MKLweKey* MKlwekey, const MKRLweKey *MKrlwekey,
                 MKLweSample *one)
{
    for (auto x: ord->buy){
        CktAdd(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey, accTmp1, accBuy, x);
        for (int i = 0; i < WIDTH; i++){
            MKlweCopy(&accBuy[i], &accTmp1[i], MKparams);
        }
    }

    for (auto x: ord->sell){
        CktAdd(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey, accTmp2, accSell, x);
        for (int i = 0; i < WIDTH; i++){
            MKlweCopy(&accSell[i], &accTmp2[i], MKparams);
        }
    }

    auto sellGRTbuy = new_MKLweSample(LWEparams, MKparams);
    CktGrt(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKlwekey, MKrlwekey, sellGRTbuy, accSell, accBuy, one);

    auto total1 = new_MKLweSample_array(WIDTH, LWEparams, MKparams);

    auto total2 = new_MKLweSample_array(WIDTH, LWEparams, MKparams);

    auto totalTmp = new_MKLweSample_array(WIDTH, LWEparams, MKparams);

    for (int i = 0; i < WIDTH; i++){
        MKbootsMUX(&total1[i], sellGRTbuy, &accBuy[i], &accSell[i], bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
        MKbootsMUX(&total2[i], sellGRTbuy, &accBuy[i], &accSell[i], bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
    }

    auto ordLeq = new_MKLweSample(LWEparams, MKparams);

    int m = ord->buy.size();
    for (int i = 0; i < m; i++){
        // if b <= total, res = b else res = total, total -= res
        CktLeq(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKlwekey, MKrlwekey, ordLeq, ord->buy[i], total1, one);
        MKLweSample *res = new_MKLweSample_array(WIDTH, LWEparams, MKparams);

        for (int j = 0; j < WIDTH; j++){
            MKbootsMUX(&res[j], ordLeq, &ord->buy[i][j], &total1[j], bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
        }
        CktSub(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKlwekey, MKrlwekey, totalTmp, total1, res, one);
        for (int j = 0; j < WIDTH; j++){
            MKlweCopy(&total1[j], &totalTmp[j], MKparams);
        }

        resOrd->buy.push_back(res);
    }


    int n = ord->sell.size();
    for (int i = 0; i < n; i++){
        // if s <= total, res = s else res = total, total -= res
        CktLeq(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKlwekey, MKrlwekey, ordLeq, ord->sell[i], total2, one);
        MKLweSample *res = new_MKLweSample_array(WIDTH, LWEparams, MKparams);

        for (int j = 0; j < WIDTH; j++){
            MKbootsMUX(&res[j], ordLeq, &ord->sell[i][j], &total2[j], bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);
        }
        CktSub(bkFFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKlwekey, MKrlwekey, totalTmp, total2, res, one);
        for (int j = 0; j < WIDTH; j++){
            MKlweCopy(&total2[j], &totalTmp[j], MKparams);
        }

        resOrd->sell.push_back(res);
    }
}



int main()
{
    // auto tfheParams = new_default_gate_bootstrapping_parameters(110);
    // auto params = tfheParams->in_out_params;
    // auto sk = new_random_gate_bootstrapping_secret_keyset(tfheParams);
    // auto bk = &sk->cloud;

    static const int32_t k = 1;
    static const double ks_stdev = 3.05e-6;// 2.44e-5; //standard deviation
    static const double bk_stdev = 3.72e-10; // 3.29e-10; //standard deviation
    static const double max_stdev = 0.001; //max standard deviation for a 1/4 msg space
    static const int32_t n = 560; //500;            // LWE modulus
    static const int32_t n_extract = 1024;    // LWE extract modulus (used in bootstrapping)
    static const int32_t hLWE = 0;         // HW secret key LWE --> not used
    static const double stdevLWE = 0.001;      // LWE ciphertexts standard deviation
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


    // Input format:
    // <#sell> <#buy>
    // <sell orders space separated>
    // <buy orders space separated>

    vector<int> sellOrd;
    vector<int> buyOrd;

    int ns, m, tmp;
    cout << "Enter the volumes: " << endl;
    cin >> ns >> m;
    for (int i = 0; i < ns; i++){
        cin >> tmp;
        if (tmp < 0){
            cerr << "Order cannot be negative. Skipping " << tmp << endl;
        }
        sellOrd.push_back(tmp);
    }

    for (int i = 0; i < m; i++){
        cin >> tmp;
        if (tmp < 0){
            cerr << "Order cannot be negative. Skipping " << tmp << endl;
        }
        buyOrd.push_back(tmp);
    }

    cout << "Input DONE!" << endl;

    EncOrders ord, resOrd;

    clock_t begin_Enc = clock();

    for (int s: sellOrd){
        auto encS = new_MKLweSample_array(WIDTH, LWEparams, MKparams);
        IntSymEncrypt(encS, s, MKlwekey);
        ord.sell.push_back(encS);
    }

    for (int b: buyOrd){
        auto encB = new_MKLweSample_array(WIDTH, LWEparams, MKparams);
        IntSymEncrypt(encB, b, MKlwekey);
        ord.buy.push_back(encB);
    }

    auto accBuy = new_MKLweSample_array(WIDTH, LWEparams, MKparams);
    auto accSell = new_MKLweSample_array(WIDTH, LWEparams, MKparams);
    auto accTmp1 = new_MKLweSample_array(WIDTH, LWEparams, MKparams);
    auto accTmp2 = new_MKLweSample_array(WIDTH, LWEparams, MKparams);
    auto one = new_MKLweSample(LWEparams, MKparams);


    IntSymEncrypt(accBuy, 0, MKlwekey);
    IntSymEncrypt(accSell, 0, MKlwekey);
    IntSymEncrypt(accTmp1, 0, MKlwekey);
    IntSymEncrypt(accTmp2, 0, MKlwekey);
    MKbootsSymEncrypt(one, 1, MKlwekey);

    VolumeMatch(&ord, &resOrd, accBuy, accSell, accTmp1, accTmp2, MKlweBK_FFT, LWEparams, extractedLWEparams, 
    RLWEparams, MKparams, MKlwekey, MKrlwekey, one);

    clock_t end_Enc = clock();
    double time_Enc = ((double) end_Enc - begin_Enc)/CLOCKS_PER_SEC;

    cout << "Finished Time: " << time_Enc << "seconds" << endl;

    cout << "Resulting Sell:" << endl;
    for (auto x: resOrd.sell){
        cout << IntSymDecrypt(x, MKlwekey) << endl;
    }

    cout << "Resulting Buy:" << endl;
    for (auto x: resOrd.buy){
        cout << IntSymDecrypt(x, MKlwekey) << endl;
    }


    // int bit1;
    // int bit2;
    // int bit3;

    // cout << "Enter the inputs: " << endl;

    // for (int i=0; i < 4; i++)
    // {
    //     cin >> bit1 >> bit2 >> bit3;

    //     cout << bit1 << " " << bit2 << " " << bit3 << endl;

    //     auto a = new_MKLweSample_array(WIDTH, LWEparams, MKparams);
    //     IntSymEncrypt(a, bit1, MKlwekey);

    //     auto b = new_MKLweSample_array(WIDTH, LWEparams, MKparams);
    //     IntSymEncrypt(b, bit2, MKlwekey);

    //     auto c = new_MKLweSample_array(WIDTH, LWEparams, MKparams);
    //     IntSymEncrypt(c, bit3, MKlwekey);

    //     auto res = new_MKLweSample_array(WIDTH, LWEparams, MKparams);
    //     IntSymEncrypt(res, 0, MKlwekey);

    //     CktLeq(MKlweBK_FFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKlwekey, MKrlwekey, res, a, b, c);

    //     cout << IntSymDecrypt(res, MKlwekey) << endl;

    // }

    // cout << "Enter the inputs: " << endl;

    // for (int i=0; i < 2; i++)
    // {
    //     cin >> bit1 >> bit2 >> bit3;

    //     cout << bit1 << " " << bit2 << " " << bit3 << endl;

    //     auto a = new_MKLweSample(LWEparams, MKparams);
    //     MKbootsSymEncrypt(a, bit1, MKlwekey);

    //     auto b = new_MKLweSample(LWEparams, MKparams);
    //     MKbootsSymEncrypt(b, bit2, MKlwekey);

    //     auto c = new_MKLweSample(LWEparams, MKparams);
    //     MKbootsSymEncrypt(c, bit3, MKlwekey);

    //     auto res = new_MKLweSample(LWEparams, MKparams);

    //     MKbootsMUX(res, a, b, c, MKlweBK_FFT, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);

    //     cout << MKbootsSymDecrypt(res, MKlwekey) << endl;

    // }


    return 0;
}


