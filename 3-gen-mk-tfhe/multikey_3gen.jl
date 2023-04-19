include("./src/TFHE.jl")
using Random, Printf
using .TFHE


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


    # # Boolean Gate Testing

    # for trial=1:10
    #     mess1 = true
    #     mess2 = true
    #     mess3 = false
    #     out = (mess1 && mess2 && mess3)

    #     println(" \n\n(3) Trial - $trial: $mess1 AND $mess2 AND $mess3 = $out")

    #     enc_mess1 = mk_encrypt_3gen(rng, secret_keys, mess1)
    #     enc_mess2 = mk_encrypt_3gen(rng, secret_keys, mess2)
    #     enc_mess3 = mk_encrypt_3gen(rng, secret_keys, mess3)

    #     # @time enc_out =  mk_gate_3and_3gen(bk_keys, ks_keys, enc_mess1, enc_mess2, enc_mess3)
    #     @time enc_out =  mk_gate_3and_3gen(bk_keys, ks_keys, enc_mess1, enc_mess2, enc_mess3)
    #     dec_out = mk_decrypt_3gen(secret_keys, enc_out)
    #     println("Final result -> Original output: ", out, ", Decrypted output: ", dec_out)
        
    # end

    # # Integer Circuit Testing

    WIDTH = 8

    for i=1:5
        msg1 = rand(1:10)
        msg2 = rand(1:10)

        # msg1 = -msg1
        # msg2 = -msg2

        println("msg1: ", msg1)
        println("msg2: ", msg2)
        cin = false

        ct1 = mk_int_encrypt_3gen(rng, secret_keys, msg1, WIDTH)
        ct2 = mk_int_encrypt_3gen(rng, secret_keys, msg2, WIDTH)

        println("ct1: ", mk_int_decrypt_3gen(secret_keys, ct1, WIDTH))
        println("ct2: ", mk_int_decrypt_3gen(secret_keys, ct2, WIDTH))

        ZERO = mk_encrypt_3gen(rng, secret_keys, cin)
        println("Cin: ", mk_decrypt_3gen(secret_keys, ZERO))

        @time ct_res = mk_add_3gen_v2(bk_keys, ks_keys, ct1, ct2, ZERO, WIDTH)

        result = mk_int_decrypt_3gen(secret_keys, ct_res, WIDTH)

        println("result: ", result)

    end

end


main()