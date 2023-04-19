include("./src/TFHE.jl")
using Random, Printf
using .TFHE

using CUDA
using BenchmarkTools
using CUDAKernels, KernelAbstractions
import Adapt

# const Torus32 = Int32
# const Torus64 = Int64

# function mk_lwe_noiseless_trivial_gpu(mu::Torus32, params::LweParams, parties::Int)
#     MKLweSampleGPU(params, CUDA.zeros(typeof(mu), params.size, parties), mu, 0.)
# end

# function mk_gate_xor_3gen_gpu(bk, ks, x::MKLweSampleGPU, y::MKLweSampleGPU)
#     temp = (
#         mk_lwe_noiseless_trivial_gpu(encode_message(1, 4), x.params, length(bk))
#         + convert(Torus32, 2)*x + convert(Torus32, 2)*y)
#     # bk[1].rlwe_params.is32 ? encode = encode_message : encode = encode_message64
#     # mk_bootstrap_3gen(bk,ks, encode(1, 8), temp)

#     return
# end

# Adapt.@adapt_structure MKLweSampleGPU

function main()
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



    # for trial=1:5
    #     select = true
    #     m1 = true
    #     m2 = false
    #     out = select ? m1 : m2

    #     c1 = mk_encrypt_3gen(rng, secret_keys, m1)
    #     c2 = mk_encrypt_3gen(rng, secret_keys, m2)
    #     s1 = mk_encrypt_3gen(rng, secret_keys, select)

    #     println("dec of select:", mk_decrypt_3gen(secret_keys, s1))
    #     println("dec of c1:", mk_decrypt_3gen(secret_keys, c1))
    #     println("dec of c2:", mk_decrypt_3gen(secret_keys, c2))

    #     @time enc_out = mk_gate_mux_3gen(bk_keys, ks_keys, s1, c1, c2)
    #     dec_out = mk_decrypt_3gen(secret_keys, enc_out)
    #     println("Final result -> Original output: ", out, ", Decrypted output: ", dec_out)
        
    # end

    # WIDTH = 8

    # for i=1:5
    #     msg1 = rand(1:10)
    #     msg2 = rand(1:10)

    #     msg1 = -msg1
    #     # msg2 = -msg2

    #     println("msg1: ", msg1)
    #     println("msg2: ", msg2)
    #     cin = false

    #     ct1 = mk_int_encrypt_3gen(rng, secret_keys, msg1, WIDTH)
    #     ct2 = mk_int_encrypt_3gen(rng, secret_keys, msg2, WIDTH)
    #     ZERO = mk_encrypt_3gen(rng, secret_keys, cin)

    #     @time ct_res = mk_int_mul_3gen(bk_keys, ks_keys, ct1, ct2, ZERO, WIDTH)

    #     result = mk_int_decrypt_3gen(secret_keys, ct_res, WIDTH)

    #     println("result: ", result)

    # end

    # matrix multiply

    # input_size = 28
    # kernel_size = 3
    # number_kernels = 16

    # input = Array{MKLweSample, 2}(undef, input_size, input_size)
    # kernels = Array{MKLweSample, 3}(undef, number_kernels, kernel_size, kernel_size)

    # ZERO = mk_encrypt_3gen(rng, secret_keys, false)

    # for c = 1:number_kernels
    #     for i = 1:kernel_size
    #         for j = 1:kernel_size
    #             kernels[c, i, j] = ZERO
    #         end
    #     end
    # end

    # kernels_gpu = cu(kernels)
    # bk_keys_gpu = cu(bk_keys)
    # ks_keys_gpu = cu(ks_keys)

    # println(typeof(kernels_gpu))
    # println(typeof(bk_keys_gpu))
    # println(typeof(ks_keys_gpu))

    # for c = 1:number_kernels
    #     for i = 1:kernel_size
    #         for j = 1:kernel_size
    #             println(mk_decrypt_3gen(secret_keys, kernels[c, i, j]))
    #         end
    #     end
    # end

    # result = mk_decrypt_3gen(secret_keys, kernels[1, 1, 1])

    # println("result: ", result)

    bk_keys_gpu = cu(bk_keys)
    ks_keys_gpu = cu(ks_keys)

    WIDTH = 8

    for i=1:5

        # select = true
        m1 = true
        m2 = false
        # out = select ? m1 : m2

        c1 = mk_encrypt_3gen(rng, secret_keys, m1)
        c2 = mk_encrypt_3gen(rng, secret_keys, m2)
        # s1 = mk_encrypt_3gen(rng, secret_keys, select)

        # println("dec of select:", mk_decrypt_3gen(secret_keys, s1))
        println("dec of c1:", mk_decrypt_3gen(secret_keys, c1))
        println("dec of c2:", mk_decrypt_3gen(secret_keys, c2))

        c1_gpu = MKLweSampleGPU(c1.params, cu(c1.a), c1.b, c1.current_variance)
        c2_gpu = MKLweSampleGPU(c2.params, cu(c2.a), c2.b, c2.current_variance)
        # s1_gpu = MKLweSampleGPU(s1.params, cu(s1.a), s1.b, s1.current_variance)

        println(isbitstype(typeof(c1_gpu)))
        println(isbitstype(typeof(c2_gpu)))

        @cuda threads=1024 mk_gate_xor_3gen_gpu(bk_keys_gpu, ks_keys_gpu, c1_gpu, c2_gpu)
        # dec_out = mk_decrypt_3gen(secret_keys, enc_out)
        # println("Final result -> Original output: ", out, ", Decrypted output: ", dec_out)


        # ct_res = Array(ct_res_gpu)
        # result = mk_int_decrypt_3gen(secret_keys, ct_res, WIDTH)

        # println("result: ", result)

    end



end


main()