module TFHE

using Random: AbstractRNG
using LinearAlgebra: mul!
using GenericFFT: plan_fft, plan_ifft, Plan
import DarkIntegers: mul_by_monomial
using DarkIntegers: Polynomial, negacyclic_modulus, mul_naive
using DoubleFloats: Double64

include("numeric-functions.jl")
export encode_message
export decode_message
export encode_message64
export decode_message64
export noise_calc
export rand_uniform_torus32
export rand_gaussian_torus32


include("polynomials.jl")
export torus_polynomial
export TorusPolynomial
export transformed_mul
export int_polynomial
export torus_polynomial_

include("lwe.jl")
export LweKey
export lwe_phase

include("rlwe.jl")
export RLweKey
export rlwe_noiseless_trivial
export rlwe_encrypt_zero
export extract_lwe_key

include("tgsw.jl")
export decompose

include("tlev.jl")

include("keyswitch.jl")
export KeyswitchKey

include("bootstrap.jl")

include("api.jl")
export make_key_pair
export LweSample
export SecretKey
export CloudKey
export encrypt
export decrypt
export tfhe_parameters_80
export tfhe_parameters_128
export lwe_parameters
export rlwe_parameters
export tgsw_parameters
export keyswitch_parameters

export SecretKey_new
export CloudKey_new

export SecretKey_3gen
export CloudKey_3gen


include("gates.jl")
export gate_nand
export gate_or
export gate_and
export gate_xor
export gate_xnor
export gate_not
export gate_constant
export gate_nor
export gate_andny
export gate_andyn
export gate_orny
export gate_oryn
export gate_mux

include("mk_internals.jl")
export CRP_3gen
export MKLweSample
export PublicKey
export CommonPubKey_3gen
export mk_lwe_noiseless_trivial
export mk_keyswitch
export mk_keyswitch_3gen
export mk_lwe_phase
export mk_bootstrap
export mk_bootstrap_wo_keyswitch

export MKLweSampleGPU
export MKLweSample
# export mk_lwe_noiseless_trivial_gpu

include("tgsw_3gen.jl")
export TGswSample_3gen
export TransformedTGswSample_3gen
export RgswParts_2_3_3gen
export RgswPart_1_3gen
export tgsw_encrypt_3gen
export tgsw_encrypt_3gen_wo_FFT
export tgsw_extern_mul_3gen


include("new_mk_internals.jl")
export mk_bootstrap_new
export mk_bootstrap_new_wo_FFT

include("3gen_mk_internals.jl")

export test
export BootstrapKeyPart_3gen
export TransformedBootstrapKeyPart_3gen
export mk_blind_rotate_and_extract_3gen
export mk_bootstrap_3gen

include("mk_api.jl")
export SharedKey
export CloudKeyPart
export MKCloudKey
export MKCloudKey_new_wo_FFT
export mk_encrypt
export mk_decrypt
export mktfhe_parameters_2party
export mktfhe_parameters_4party
export mktfhe_parameters_8party
export mktfhe_parameters_16party
export mk_decrypt_3gen
export SharedKey_new
#~ export SharedKey_3gen
export GenCRP_3gen
export CloudKeyPart_new
export MKCloudKey_new
export mk_encrypt_new
export mk_encrypt_3gen
export mk_int_encrypt_3gen
export mk_decrypt_new
export mk_decrypt_3gen
export mk_int_decrypt_3gen
export mktfhe_parameters_2party_new
export mktfhe_parameters_2party_fast
export mktfhe_parameters_2party_3gen   # for now only these
export mktfhe_parameters_3party_3gen
export mktfhe_parameters_4party_new
export mktfhe_parameters_4party_fast
export mktfhe_parameters_4party_3gen
export mktfhe_parameters_5party_3gen
export mktfhe_parameters_8party_new
export mktfhe_parameters_8party_fast
export mktfhe_parameters_8party_3gen
export mktfhe_parameters_16party_new
export mktfhe_parameters_16party_fast
export mktfhe_parameters_16party_3gen
export mktfhe_parameters_32party_new
export mktfhe_parameters_32party_fast
export mktfhe_parameters_32party_3gen
export mktfhe_parameters_32party_3gen
export mktfhe_parameters_64party_3gen
export mktfhe_parameters_128party_3gen
export mktfhe_parameters_256party_3gen
export mktfhe_parameters_512party_3gen

# export mk_encrypt_3gen_gpu

include("mk_gates.jl")
export mk_gate_nand
# export mk_gate_mux

include("new_mk_gates.jl")
export mk_gate_nand_new
export mk_gate_nand_new_wo_FFT

include("3gen_mk_gates.jl")
export mk_gate_nand_3gen
export mk_gate_or_3gen
export mk_gate_xor_3gen
export mk_gate_and_3gen
export mk_gate_3and_3gen
export mk_gate_not_3gen
export mk_gate_mux_3gen
export mk_copy_3gen
export mk_add_3gen
export mk_add_3gen_v2
export mk_inv_3gen
export mk_sub_3gen
export mk_less_3gen
export mk_grt_3gen
export mk_leq_3gen
export mk_geq_3gen

export mk_int_add_with_carry_3gen
export mk_int_mul_3gen

export conv2d_clear

export mk_gate_xor_3gen_gpu
# export mk_int_add_3gen_gpu
end
