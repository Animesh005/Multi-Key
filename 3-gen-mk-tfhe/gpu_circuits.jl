include("./src/TFHE.jl")
using Random, Printf
using .TFHE

using CUDA
using BenchmarkTools
using CUDAKernels, KernelAbstractions
import Adapt

const Torus32 = Int32
const Torus64 = Int64

# Adapt.@adapt_structure MKLweSample

# function Adapt.adapt_structure(to, mkls::MKLweSample)
#     params = Adapt.adapt_structure(to, mkls.params)
#     a = Adapt.adapt_structure(to, mkls.a)
#     b = Adapt.adapt_structure(to, mkls.b)
#     current_variance = Adapt.adapt_structure(to, mkls.current_variance)
#     MKLweSample(params, a, b, current_variance)
# end

function mk_lwe_noiseless_trivial_gpu(mu::Torus32, params, parties::Int)
    MKLweSampleGPU(params, CUDA.zeros(typeof(mu), params.size, parties), mu, 0.)
end

function xor_3gen_gpu(bk, ks, x, y)
    temp = (
        mk_lwe_noiseless_trivial_gpu(encode_message(1, 4), x.params, length(bk))
        + convert(Torus32, 2)*x + convert(Torus32, 2)*y)

    # bk[1].rlwe_params.is32 ? encode = encode_message : encode = encode_message64
    # mk_bootstrap_3gen(bk,ks, encode(1, 8), temp)

    # return 
end


parties = 2

params = mktfhe_parameters_2party_3gen

rng = MersenneTwister()

@printf("3rd MK-TFHE - %s parties\n========\n(3) KEY GENERATION AND PRECOMP ...\n",parties)

secret_keys = [SecretKey_3gen(rng, params) for _ in 1:parties]

rlwe_keys = [RLweKey(rng,rlwe_parameters(params),true) for _ in 1:parties]

precomp_time = @elapsed crp_a = CRP_3gen(rng, tgsw_parameters(params), rlwe_parameters(params),true)

precomp_time += @elapsed pubkeys=[PublicKey(rng,rlwe_keys[i],params.gsw_noise_stddev,crp_a,tgsw_parameters(params),1) for i=1:parties] # Generation of the individual public keys.

precomp_time += @elapsed common_pubkey=CommonPubKey_3gen(pubkeys, params, parties)  #generation of the common public key.

precomp_time += @elapsed bk_keys = [BootstrapKeyPart_3gen(rng, secret_keys[i].key, params.gsw_noise_stddev,crp_a,
            common_pubkey, tgsw_parameters(params), rlwe_parameters(params),1) for i in 1:parties]

precomp_time+= @elapsed bk_keys=[TransformedBootstrapKeyPart_3gen(bk_keys[i]) for i in 1:parties]

precomp_time+= @elapsed ks_keys = [KeyswitchKey(rng,params.ks_noise_stddev, keyswitch_parameters(params),secret_keys[i].key,rlwe_keys[i]) for i in 1:parties]



@printf("(3) PRECOMP TIME : %s seconds",precomp_time)

getsize(var) = Base.format_bytes(Base.summarysize(var)/parties)

@printf("(3) BK SIZE : %s, KSK SIZE : %s\n\n", getsize(bk_keys), getsize(ks_keys))

bk_keys_gpu = cu(bk_keys)
ks_keys_gpu = cu(ks_keys)

WIDTH = 8

m1 = true
m2 = true
out = xor(m1, m2)

c1 = mk_encrypt_3gen(rng, secret_keys, m1)
c2 = mk_encrypt_3gen(rng, secret_keys, m2)

# Adapt.@adapt_structure MKLweSampleGPU

c1_gpu = MKLweSampleGPU(c1.params, CuArray(c1.a), c1.b, c1.current_variance)
c2_gpu = MKLweSampleGPU(c2.params, CuArray(c2.a), c2.b, c2.current_variance)


println(typeof(c1_gpu))
println(typeof(c2_gpu))

println(typeof(c1_gpu.a))
println(typeof(c2_gpu.a))

result_gpu = xor_3gen_gpu(bk_keys_gpu, ks_keys_gpu, c1_gpu, c2_gpu)
println(typeof(result_gpu))

result = MKLweSample(result_gpu.params, Array(result_gpu.a), result_gpu.b, result_gpu.current_variance)

dec_out = mk_decrypt_3gen(secret_keys, result)
println("Final result -> Original output: ", out, ", Decrypted output: ", dec_out)
