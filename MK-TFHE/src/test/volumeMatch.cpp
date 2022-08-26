#include "tfhe.h"
#include "tfhe_io.h"
#include <bits/stdc++.h>

#define WIDTH 8

using namespace std;


void CktAdd(const LweParams *params, const TFheGateBootstrappingCloudKeySet *bk,
            LweSample *res, LweSample *a, LweSample *b, LweSample *Cin = NULL)
{
    auto carry = new_LweSample(params);
    auto tmp1 = new_LweSample(params);
    auto tmp2 = new_LweSample(params);
    auto tmp3 = new_LweSample(params);

    auto _cin = Cin;

    for (int i = 0; i < WIDTH; i++){

        bootsXOR(tmp1, &a[i], &b[i], bk);   // tmp1 = a^b
        bootsAND(tmp2, &a[i], &b[i], bk);   // tmp2 = ab
        if (_cin){
            bootsXOR(&res[i], tmp1, _cin, bk);  // res = Cin^a^b
            bootsAND(tmp3, tmp1, _cin, bk);
            bootsOR(carry, tmp2, tmp3, bk);    // carry = ab + Cin(a^b)  
        }else{
            bootsCOPY(&res[i], tmp1, bk);
            bootsCOPY(carry, tmp2, bk);
        }

        _cin = carry;

    }

    delete_LweSample(carry);
    delete_LweSample(tmp1);
    delete_LweSample(tmp2);
    delete_LweSample(tmp3);
}

void CktInv(const LweParams *params, const TFheGateBootstrappingCloudKeySet *bk,
            LweSample *res, LweSample *a, LweSample *one)
{
    for (int i = 0; i < WIDTH; i++){
        bootsXOR(&res[i], &a[i], one, bk);
    }
}

void CktSub(const LweParams *params, const TFheGateBootstrappingCloudKeySet *bk,
            LweSample *res, LweSample *a, LweSample *b, LweSample *one)
{
    auto tmp = new_LweSample_array(WIDTH, params);
    CktInv(params, bk, tmp, b, one);
    CktAdd(params, bk, res, a, tmp, one);
    delete_LweSample_array(WIDTH, tmp);
}

void CktLess(const LweParams *params, const TFheGateBootstrappingCloudKeySet *bk,
            LweSample *res, LweSample *a, LweSample *b, LweSample *one)     // res = (a < b)
{
    auto tmp = new_LweSample_array(WIDTH, params);
    CktSub(params, bk, tmp, a, b, one);
    bootsCOPY(res, &tmp[WIDTH-1], bk);
    delete_LweSample_array(WIDTH, tmp);
}

void CktGrt(const LweParams *params, const TFheGateBootstrappingCloudKeySet *bk,
            LweSample *res, LweSample *a, LweSample *b, LweSample *one)     // res = (a > b)
{
    auto tmp = new_LweSample_array(WIDTH, params);
    CktSub(params, bk, tmp, b, a, one);
    bootsCOPY(res, &tmp[WIDTH-1], bk);
    delete_LweSample_array(WIDTH, tmp);
}

void CktGeq(const LweParams *params, const TFheGateBootstrappingCloudKeySet *bk,
            LweSample *res, LweSample *a, LweSample *b, LweSample *one)     // res = (a >= b)
{
    auto tmp = new_LweSample(params);
    CktLess(params, bk, tmp, a, b, one);
    bootsXOR(res, tmp, one, bk);
    delete_LweSample(tmp);
}


void CktLeq(const LweParams *params, const TFheGateBootstrappingCloudKeySet *bk,
            LweSample *res, LweSample *a, LweSample *b, LweSample *one)     // res = (a <= b)
{
    auto tmp = new_LweSample(params);
    CktGrt(params, bk, tmp, a, b, one);
    bootsXOR(res, tmp, one, bk);
    delete_LweSample(tmp);
}

void CktEq(const LweParams *params, const TFheGateBootstrappingCloudKeySet *bk,
            LweSample *res, LweSample *a, LweSample *b, LweSample *one)     // res = (a == b)
{
    auto grt = new_LweSample(params);
    auto lss = new_LweSample(params);

    CktGrt(params, bk, grt, a, b, one);
    CktLess(params, bk, lss, a, b, one);

    auto gol = new_LweSample(params);
    bootsOR(gol, grt, lss, bk);
    bootsXOR(res, gol, one, bk);

    delete_LweSample(grt);
    delete_LweSample(lss);
    delete_LweSample(gol);
}

// Buy and Sell order ints should not be longer than WIDTH bits.
struct Orders
{
    vector<int> buy;
    vector<int> sell;
};

struct EncOrders
{
    vector<LweSample *> buy;
    vector<LweSample *> sell;
};

void VolumeMatch(EncOrders *ord, EncOrders *resOrd,
                 LweSample *accBuy, LweSample *accSell,
                 LweSample *accTmp1, LweSample *accTmp2,
                 const LweParams *params, const TFheGateBootstrappingCloudKeySet *bk,
                 LweSample *one)
{
    for (auto x: ord->buy){
        CktAdd(params, bk, accTmp1, accBuy, x);
        for (int i = 0; i < WIDTH; i++){
            bootsCOPY(&accBuy[i], &accTmp1[i], bk);
        }
    }

    for (auto x: ord->sell){
        CktAdd(params, bk, accTmp2, accSell, x);
        for (int i = 0; i < WIDTH; i++){
            bootsCOPY(&accSell[i], &accTmp2[i], bk);
        }
    }

    auto sellGRTbuy = new_LweSample(params);
    CktGrt(params, bk, sellGRTbuy, accSell, accBuy, one);

    auto total1 = new_LweSample_array(WIDTH, params);
    auto total2 = new_LweSample_array(WIDTH, params);
    auto totalTmp = new_LweSample_array(WIDTH, params);

    for (int i = 0; i < WIDTH; i++){
        bootsMUX(&total1[i], sellGRTbuy, &accBuy[i], &accSell[i], bk);
        bootsMUX(&total2[i], sellGRTbuy, &accBuy[i], &accSell[i], bk);
    }

    auto ordLeq = new_LweSample(params);

    int m = ord->buy.size();
    for (int i = 0; i < m; i++){
        // if b <= total, res = b else res = total, total -= res
        CktLeq(params, bk, ordLeq, ord->buy[i], total1, one);
        LweSample *res = new_LweSample_array(WIDTH, params);
        for (int j = 0; j < WIDTH; j++){
            bootsMUX(&res[j], ordLeq, &ord->buy[i][j], &total1[j], bk);
        }
        CktSub(params, bk, totalTmp, total1, res, one);
        for (int j = 0; j < WIDTH; j++){
            bootsCOPY(&total1[j], &totalTmp[j], bk);
        }

        resOrd->buy.push_back(res);
    }


    int n = ord->sell.size();
    for (int i = 0; i < n; i++){
        // if s <= total, res = s else res = total, total -= res
        CktLeq(params, bk, ordLeq, ord->sell[i], total2, one);
        LweSample *res = new_LweSample_array(WIDTH, params);
        for (int j = 0; j < WIDTH; j++){
            bootsMUX(&res[j], ordLeq, &ord->sell[i][j], &total2[j], bk);
        }
        CktSub(params, bk, totalTmp, total2, res, one);
        for (int j = 0; j < WIDTH; j++){
            bootsCOPY(&total2[j], &totalTmp[j], bk);
        }

        resOrd->sell.push_back(res);
    }
}





void IntSymEncrypt(LweSample *res, int p, TFheGateBootstrappingSecretKeySet *sk)
{
    for (int i = 0; i < WIDTH; i++){
        int bit = p & 1;
        p = (p >> 1);
        bootsSymEncrypt(&res[i], bit, sk);
    }
}

int IntSymDecrypt(LweSample *c, TFheGateBootstrappingSecretKeySet *sk)
{
    int msb = bootsSymDecrypt(&c[WIDTH-1], sk);

    int ans = 0;
    for (int i = 0; i < WIDTH - 1; i++){
        int bit = bootsSymDecrypt(&c[i], sk);
        ans += (bit ^ msb) << i;     // If msb == 1, invert
    }

    if (msb == 1){
        ans++;
        ans = -ans;
    }

    return ans;
}

int main()
{
    auto tfheParams = new_default_gate_bootstrapping_parameters(110);
    auto params = tfheParams->in_out_params;
    auto sk = new_random_gate_bootstrapping_secret_keyset(tfheParams);\
    auto bk = &sk->cloud;

    // Input format:
    // <#sell> <#buy>
    // <sell orders space separated>
    // <buy orders space separated>

    // vector<int> sellOrd;
    // vector<int> buyOrd;

    // int n, m, tmp;
    // cin >> n >> m;
    // for (int i = 0; i < n; i++){
    //     cin >> tmp;
    //     if (tmp < 0){
    //         cerr << "Order cannot be negative. Skipping " << tmp << endl;
    //     }
    //     sellOrd.push_back(tmp);
    // }

    // for (int i = 0; i < m; i++){
    //     cin >> tmp;
    //     if (tmp < 0){
    //         cerr << "Order cannot be negative. Skipping " << tmp << endl;
    //     }
    //     buyOrd.push_back(tmp);
    // }

    // EncOrders ord, resOrd;

    // clock_t begin_Enc = clock();

    // for (int s: sellOrd){
    //     auto encS = new_LweSample_array(WIDTH, params);
    //     IntSymEncrypt(encS, s, sk);
    //     ord.sell.push_back(encS);
    // }

    // for (int b: buyOrd){
    //     auto encB = new_LweSample_array(WIDTH, params);
    //     IntSymEncrypt(encB, b, sk);
    //     ord.buy.push_back(encB);
    // }

    // auto accBuy = new_LweSample_array(WIDTH, params);
    // auto accSell = new_LweSample_array(WIDTH, params);
    // auto accTmp1 = new_LweSample_array(WIDTH, params);
    // auto accTmp2 = new_LweSample_array(WIDTH, params);
    // auto one = new_LweSample(params);


    // IntSymEncrypt(accBuy, 0, sk);
    // IntSymEncrypt(accSell, 0, sk);
    // IntSymEncrypt(accTmp1, 0, sk);
    // IntSymEncrypt(accTmp2, 0, sk);
    // bootsSymEncrypt(one, 1, sk);

    // VolumeMatch(&ord, &resOrd, accBuy, accSell, accTmp1, accTmp2, params, bk, one);

    // clock_t end_Enc = clock();
    // double time_Enc = ((double) end_Enc - begin_Enc)/CLOCKS_PER_SEC;

    // cout << "Finished Time: " << time_Enc << "seconds" << endl;

    // cout << "Resulting Sell:" << endl;
    // for (auto x: resOrd.sell){
    //     cout << IntSymDecrypt(x, sk) << endl;
    // }

    // cout << "Resulting Buy:" << endl;
    // for (auto x: resOrd.buy){
    //     cout << IntSymDecrypt(x, sk) << endl;
    // }

    int32_t bit1 = 13;
    int32_t bit2 = 17;
    int32_t bit3 = 1;

    auto a = new_LweSample_array(WIDTH, params);
    IntSymEncrypt(a, bit1, sk);

    auto b = new_LweSample_array(WIDTH, params);
    IntSymEncrypt(b, bit2, sk);

    auto c = new_LweSample_array(WIDTH, params);
    IntSymEncrypt(c, bit3, sk);

    auto one = new_LweSample(params);
    bootsSymEncrypt(one, 1, sk);

    auto res = new_LweSample_array(WIDTH, params);
    IntSymEncrypt(res, 0, sk);

    // CktAdd(LWEparams, extractedLWEparams, RLWEparams, MKparams, res, a, b);
    // MKlweAddTo(a, b, MKparams);
    // MKlweCopy(res, a, MKparams);

    CktSub(params, bk, res, a, b, one);

    cout << IntSymDecrypt(res, sk) << endl;


    return 0;
}


