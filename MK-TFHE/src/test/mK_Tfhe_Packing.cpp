#include <stdio.h>
#include <iostream>
#include <iomanip>
#include <cstdlib>
#include <cmath>
#include <sys/time.h>
#include "tfhe.h"
#include "polynomials.h"
#include "lwesamples.h"
#include "lwekey.h"
#include "lweparams.h"
#include "tlwe.h"
#include "tgsw.h"
#include "secretshare.hpp"



#include "mkTFHEparams.h"
#include "mkTFHEkeys.h"
#include "mkTFHEkeygen.h"
#include "mkTFHEsamples.h"
#include "mkTFHEfunctions.h"







using namespace std;

#define Psize 10

// MK LWE sample Packed (a_1, ..., a_k, b_1, ..., b_l)
struct MKLweSampleP {
	Torus32* a; //-- the parties*n coefs of the mask
    Torus32* b;  //
   	double current_variance; //-- average noise of the sample
   	const int32_t parties;
   	const int32_t n;

#ifdef __cplusplus
   MKLweSampleP(const LweParams* LWEparams, const MKTFHEParams* MKparams);
   ~MKLweSampleP();
   MKLweSampleP(const MKLweSample&)=delete;
   MKLweSampleP& operator=(const MKLweSampleP&)=delete;
#endif
};

MKLweSampleP* new_MKLweSampleP(const LweParams* LWEparams, const MKTFHEParams* MKparams) {
    return new MKLweSampleP(LWEparams, MKparams);
}

// MK LWE sample Packed (a_1, ..., a_k, b_1, ..., b_l)
MKLweSampleP::MKLweSampleP(const LweParams* LWEparams, const MKTFHEParams* MKparams) :
		parties(MKparams->parties), n(LWEparams->n)
{
	this->a = new Torus32[parties*n];
    this->b = new Torus32[Psize];
    this->current_variance = 0.0;
}

MKLweSampleP::~MKLweSampleP() {
    delete[] a;
}

void MKlweNoiselessTrivialP(MKLweSampleP* result, Torus32 mu, const MKTFHEParams* params){
    const int32_t parties = params->parties;
    const int32_t n = params->n;

    for (int i = 0; i < parties; ++i)
    {
        for (int j = 0; j < n; ++j)
        {
            result->a[i*n +j] = 0;
        }
    }

    for (int l=0; l < Psize; l++)
    {
      result->b[l] = mu;
    }

    result->current_variance = 0.0;
}

void MKlweSubToP(MKLweSampleP* result, const MKLweSampleP* sample, const MKTFHEParams* MKparams){
    const int32_t n = MKparams->n;
    const int32_t parties = MKparams->parties;

    for (int i = 0; i < parties; ++i)
    {
        for (int j = 0; j < n; ++j)
        {
            result->a[i*n+j] -= sample->a[i*n+j];
        }
    }

    for (int l=0; l < Psize; l++)
      result->b[l] -= sample->b[l];

    result->current_variance += sample->current_variance;
}


// **********************************************************************************
// ********************************* MAIN *******************************************
// **********************************************************************************


void dieDramatically(string message) {
    cerr << message << endl;
    abort();
}






int32_t main(int32_t argc, char **argv) {

    // generate params
    static const int32_t k = 1;
    static const double ks_stdev = 3.05e-5;// 2.44e-5; //standard deviation
    static const double bk_stdev = 3.72e-9; // 3.29e-10; //standard deviation
    static const double max_stdev = 0.012467; //max standard deviation for a 1/4 msg space
    static const int32_t n = 560; //500;            // LWE modulus
    static const int32_t n_extract = 1024;    // LWE extract modulus (used in bootstrapping)
    static const int32_t hLWE = 0;         // HW secret key LWE --> not used
    static const double stdevLWE = 0.012467;      // LWE ciphertexts standard deviation
    static const int32_t Bksbit = 2;       // Base bit key switching
    static const int32_t dks = 8;          // dimension key switching
    static const double stdevKS = ks_stdev; // 2.44e-5;       // KS key standard deviation
    static const int32_t N = 1024;            // RLWE,RGSW modulus
    static const int32_t hRLWE = 0;        // HW secret key RLWE,RGSW --> not used
    static const double stdevRLWEkey = bk_stdev; // 3.29e-10; // 0; // 0.012467;  // RLWE key standard deviation
    static const double stdevRLWE = bk_stdev; // 3.29e-10; // 0; // 0.012467;     // RLWE ciphertexts standard deviation
    static const double stdevRGSW = bk_stdev; // 3.29e-10;     // RGSW ciphertexts standard deviation
    static const int32_t Bgbit = 8;        // Base bit gadget
    static const int32_t dg = 4;           // dimension gadget
    static const double stdevBK = bk_stdev; // 3.29e-10;       // BK standard deviation
    static const int32_t parties = 4;      // number of parties

    // new parameters
    // 2 parties, B=2^9, d=3 -> works
    // 4 parties, B=2^8, d=4 -> works
    // 8 parties, B=2^6, d=5 -> works



    // params
    LweParams *LWEparams = new_LweParams(n, ks_stdev, max_stdev);
    MKTFHEParams *MKparams = new_MKTFHEParams(n, n_extract, hLWE, stdevLWE, Bksbit, dks, stdevKS, N,
                            hRLWE, stdevRLWEkey, stdevRLWE, stdevRGSW, Bgbit, dg, stdevBK, parties);
    LweParams *extractedLWEparams = new_LweParams(n_extract, ks_stdev, max_stdev);
    TLweParams *RLWEparams = new_TLweParams(N, k, bk_stdev, max_stdev);

    cout << "\nStarting key generation . . .\n" << endl;
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
    cout << "Finished key generation" << endl;
    cout << "Time for key generation: " << time_KG << " seconds" << endl;

    // SecretSharing *ss = new SecretSharing();
    // ss->shareSecret(2, 4, &(MKlwekey->key[0]), LWEparams);
    // MKKeyShare* share = new MKKeyShare();;
    // ss->GetShareSet(2, share);
    // auto tempShare = share->GetShare(1);

    // for (int i = 0; i < n; i++)
    //   cout << tempShare->key[i] << " ";
    // cout << endl;


    int32_t msg;
    int32_t msg1[Psize];
    int32_t msg2[Psize];

    // use current time as seed for the random generator
    srand(time(0));

    printf("\n1st palintext: ");
    for(int i = 0; i < Psize; i++)
    {
      msg = rand() % 2;
      msg1[i] = msg;
      printf(" %d", msg);
    }

    printf("\n2nd palintext: ");
    for(int i = 0; i < Psize; i++)
    {
      msg = rand() % 2;
      msg2[i] = msg;
      printf(" %d", msg);
    }

    // generate 2 samples in input
    MKLweSampleP *cipher0 = new_MKLweSampleP(LWEparams, MKparams);
    MKLweSampleP *cipher1 = new_MKLweSampleP(LWEparams, MKparams);

    // plaintext generation in Torus space
    Torus32 _1s8 = modSwitchToTorus32(1, 8);
    Torus32 mu1, mu2;

    for(int i=0; i < Psize; i++)
    {
      mu1 = msg1[i] ? _1s8 : -_1s8;
      mu2 = msg2[i] ? _1s8 : -_1s8;
      msg1[i] = mu1;
      msg2[i] = mu2;
    }

    double alpha = MKlwekey->MKparams->stdevLWE;

    // const int32_t n = MKlwekey->LWEparams->n;
    // const int32_t parties = MKlwekey->MKparams->parties;

    // construction of secret matrix
    Torus32 SecretMatrix[parties][Psize][n];

    for (int i=0; i < parties; i++)
    {
      for (int l = 0; l < Psize; ++l)
      {
        for (int j = 0; j < n; ++j)
        {
          SecretMatrix[i][l][j] = MKlwekey->key[i].key[j];
        }
      }
    }

    // generate extended secret matrix for decryption
    Torus32 ExtSecretMatrix[Psize][parties*n];

    for (int l = 0; l < Psize; ++l)
    {
      for (int i=0; i < parties; i++)
      {
        for (int j = 0; j < n; ++j)
        {
          ExtSecretMatrix[l][i*n+j] = SecretMatrix[i][l][j];
        }
      }
    }

    // generate vector 'a' for ciphertext

    for (int i = 0; i < parties; ++i)
    {
      for (int j = 0; j < n; ++j)
      {
        cipher0->a[i*n +j] = uniformTorus32_distrib(generator);
      }
    }

    // for (int i = 0; i < parties; ++i)
    // {
    //   for (int j = 0; j < n; ++j)
    //   {
    //     cipher1->a[i*n +j] = uniformTorus32_distrib(generator);
    //   }
    // }

    // multiply 'a' with secret matrix for msg 1


    Torus32 A[parties][Psize];

    for (int i=0; i < parties; i++)
    {
      for (int l=0; l < Psize; l++)
      {
          A[i][l] = 0;
      }
    }


    for (int i=0; i < parties; i++)
    {
      for (int l=0; l < Psize; l++)
      {
        for (int j=0; j < n; j++)
        {
          A[i][l] += ( SecretMatrix[i][l][j] * cipher0->a[i*n +j]);
        }
      }
    }

    for (int i=0; i < parties; i++)
    {
      for (int l = 0; l < Psize; ++l)
      {
        cipher0->b[l] = gaussian32(msg1[l], alpha) + A[i][l];
      }
    }

    cipher0->current_variance = alpha*alpha;

    // multiply 'a' with secret matrix for msg 2

    for (int i=0; i < parties; i++)
    {
      for (int l=0; l < Psize; l++)
      {
          A[i][l] = 0;
      }
    }

    // cout << "\nCipher 1: ";
    // for (int i=0; i < parties*n; i++)
    //   cout << " " << cipher1->a[i];

    // cout << endl;

    for (int i=0; i < parties; i++)
    {
      for (int l=0; l < Psize; l++)
      {
        for (int j=0; j < n; j++)
        {
          A[i][l] += ( SecretMatrix[i][l][j] * cipher1->a[i*n +j]);
        }
      }
    }

    for (int i=0; i < parties; i++)
    {
      for (int l = 0; l < Psize; ++l)
      {
        cipher1->b[l] = gaussian32(msg2[l], alpha) + A[i][l];
      }
    }

    cipher1->current_variance = alpha*alpha;

    cout << "\nEncryption: DONE!" << endl;

    // decryption *********************************************************************
    Torus32 ExtA[Psize];

    for (int i=0; i < Psize; i++)
    {
         ExtA[i]=0;
    }

    for (int i=0; i < Psize; i++){
      for (int j=0; j < parties * n; j++){
          ExtA[i] += ( ExtSecretMatrix[i][j] * cipher0->a[j]);
      }
    }

    Torus32 temp0[Psize]; // stores b - <a,s>
    Torus32 temp1[Psize];

    int32_t dec_msg0[Psize];
    int32_t dec_msg1[Psize];

    // decryption of 1st ciphertext

    for (int l = 0; l < Psize; ++l)
    {
      temp0[l] = cipher0->b[l] - ExtA[l];

      // printf(" \n%d, ", temp0[l]);
      if (temp0[l] > 0)
        dec_msg0[l] = 1;
      else
        dec_msg0[l] = 0;

    }

    // decryption of 2nd ciphertext

    for (int i=0; i < Psize; i++)
    {
         ExtA[i]=0;
    }

    for (int i=0; i < Psize; i++){
      for (int j=0; j < parties * n; j++){
          ExtA[i] += ( ExtSecretMatrix[i][j] * cipher1->a[j]);
      }
    }

    for (int l = 0; l < Psize; ++l)
    {
      temp1[l] = cipher1->b[l] - ExtA[l];

      // printf(" \n%d, ", temp1[l]);
      if (temp1[l] > 0)
        dec_msg1[l] = 1;
      else
        dec_msg1[l] = 0;

    }

    printf("\nDecryption ->");

    printf("\n1st decrypted msg : ");
    for (int l=0; l < Psize; l++)
    {
      printf(" %d", dec_msg0[l]);
    }

    printf("\n2nd decrypted msg : ");
    for (int l=0; l < Psize; l++)
    {
      printf(" %d", dec_msg1[l]);
    }

    cout << "\nDecryption: DONE!" << endl;


    // threshold decryption ****************************************************************************

    cout << "\nStarting thresholdization on the 1st ciphertext . . ." << endl;

    std::vector<int> subset{1, 2, 3};

    SecretSharing *ss = new SecretSharing();
    MKKeyShare* share;
    LweKey* tempShare;
    int th = 3;
    // int gropuID = 1;
    int gropuID = findGroupId(subset, th, parties);

    Torus32 PartyShareMatrix[th][parties*n];

    for (int party=0; party < parties; party++)
    {
      ss->shareSecret(th, parties, &(MKlwekey->key[party]), LWEparams);
      share = new MKKeyShare();

      for (int i=0; i < th; i++)
      {
        ss->GetShareSet(i+1, share);
        tempShare = share->GetShare(gropuID);
        for (int j=0; j < n; j++)
        {
          PartyShareMatrix[i][party*n + j] = tempShare->key[j];
        }
      }
    }

    // cout << endl;
    // for (int i=0; i < th; i++)
    // {
    //   for (int j=0; j < (parties*n); j++)
    //     cout << PartyShareMatrix[i][j] << " ";

    //   cout << endl;
    // }

    // generate extended secret matrix for partial decryption
    Torus32 ExtSecretMatrixShare[th][Psize][parties*n];

    for (int party=0; party < th; party++)
    {
      for (int l = 0; l < Psize; ++l)
      {
        for (int j=0; j < (parties*n); j++)
        {
          ExtSecretMatrixShare[party][l][j] = PartyShareMatrix[party][j];
        }
      }
    }

    // generate partial decryptions for ciphertext 1

    Torus32 PartDecArr[th][Psize];

    for (int i=0; i < th; i++)
    {
      for (int l=0; l < Psize; l++)
      {
          PartDecArr[i][l] = gaussian32(0, alpha/8);
      }
    }


    for (int i=0; i < th; i++)
    {
      for (int l=0; l < Psize; l++)
      {
        for (int j=0; j < (parties*n); j++)
        {
          PartDecArr[i][l] += ( ExtSecretMatrixShare[i][l][j] * cipher0->a[j]);
        }
      }
    }

    // cout << endl;
    // for (int i=0; i < th; i++)
    // {
    //   for (int l=0; l < Psize; l++)
    //     cout << PartDecArr[i][l] << " ";

    //   cout << endl;
    // }

    // final decryption

    for (int i=0; i < Psize; i++)
    {
         ExtA[i]=0;
    }

    for (int i=0; i < th; i++){
      for (int l=0; l < Psize; l++){
          if (i == 0)
            ExtA[l] += (PartDecArr[i][l]);
          else
            ExtA[l] += -(PartDecArr[i][l]);
      }
    }

    for (int l = 0; l < Psize; ++l)
    {
      temp0[l] = cipher0->b[l] - ExtA[l];

      // printf(" \n%d, ", temp1[l]);
      if (temp0[l] > 0)
        dec_msg0[l] = 1;
      else
        dec_msg0[l] = 0;

    }

    cout << "\n1st ciphertext -> " << th << "-out-of-" << parties << " threshold decryption: ";
    for (int l=0; l < Psize; l++)
    {
      printf(" %d", dec_msg0[l]);
    }

    cout << endl;

    


    // homomorphic NAND operation
    int32_t out;

    printf("\nNAND operation : ");
    for (int l=0; l < Psize; l++)
    {
      out = 1 - (dec_msg0[l] * dec_msg1[l]);
      printf(" %d", out);
    }

    // Torus32 MU = modSwitchToTorus32(1, 8);

    MKLweSampleP *temp_result = new_MKLweSampleP(LWEparams, MKparams);

    //compute: (0,1/8) - ca - cb
    Torus32 NandConst = modSwitchToTorus32(1, 8);
    MKlweNoiselessTrivialP(temp_result, NandConst, MKparams);
    MKlweSubToP(temp_result, cipher0, MKparams);
    MKlweSubToP(temp_result, cipher1, MKparams);

    int32_t dec_msg_nand[Psize];

    Torus32 ExtNand[Psize];
    Torus32 tempNand[Psize];

    for (int i=0; i < Psize; i++)
    {
         ExtNand[i]=0;
    }

    for (int i=0; i < Psize; i++){
      for (int j=0; j < parties * n; j++){
          ExtNand[i] += ( ExtSecretMatrix[i][j] * temp_result->a[j]);
      }
    }

    for (int l = 0; l < Psize; ++l)
    {
      tempNand[l] = temp_result->b[l] - ExtNand[l];

      // printf(" \n%d, ", tempNand[l]);
      if (tempNand[l] > 0)
        dec_msg_nand[l] = 1;
      else
        dec_msg_nand[l] = 0;

    }

    printf("\nDecrypted NAND msg : ");
    for (int l=0; l < Psize; l++)
    {
      printf(" %d", dec_msg_nand[l]);
    }

    MKLweSample *temp_result_boots = new_MKLweSample(LWEparams, MKparams);
    static const Torus32 MU = modSwitchToTorus32(1, 8);
    MKLweSample *result = new_MKLweSample(LWEparams, MKparams);
    Torus32 temp_b;
    int32_t temp_boot[Psize];

    // updating temp_result_boots

    for (int j=0; j < parties * n; j++){
      temp_result_boots->a[j] = temp_result->a[j];
    }

    cout << "\n\nStarting MK bootstrapping NAND FFT . . ." << endl;
    clock_t begin_NAND_v2m2 = clock();

    for (int i=0; i < Psize; i++)
    {
      temp_result_boots->b = temp_result->b[i];
      MKtfhe_bootstrapFFT_v2m2(result, MKlweBK_FFT, MU, temp_result_boots, LWEparams, extractedLWEparams, RLWEparams, MKparams, MKrlwekey);


    ExtNand[i]=0;

    for (int j=0; j < parties * n; j++){
        ExtNand[i] += ( ExtSecretMatrix[i][j] * result->a[j]);
    }

    temp_b = result->b - ExtNand[i];

    if (temp_b > 0)
      temp_boot[i] = 1;
    else
     temp_boot[i] = 0;

    }

    clock_t end_NAND_v2m2 = clock();
    double time_NAND_v2m2 = ((double) end_NAND_v2m2 - begin_NAND_v2m2)/CLOCKS_PER_SEC;
    cout << "Finished MK bootstrapping NAND FFT" << endl;
    cout << "Time per MK bootstrapping NAND FFT gate:  " << time_NAND_v2m2 << " seconds" << endl;

    printf("\nDecryption NAND result after bootstrapping : ");
    for (int i=0; i < Psize; i++)
    {
      printf("%d ", temp_boot[i]);
    }

    printf("\n");

    getchar();


    return 0;
}
