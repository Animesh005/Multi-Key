using Distributed

# add worker processes
proc_ids = addprocs(20)

@everywhere include("./src/TFHE.jl")
@everywhere using DistributedArrays
# @everywhere using SharedArrays
@everywhere using Random, Printf
@everywhere using .TFHE

@everywhere struct Orders
    buy :: Array{Int, 1}
    sell :: Array{Int, 1}
end

@everywhere mutable struct EncOrders
    buy :: Array{Any, 1}
    sell :: Array{Any, 1}
end

println(proc_ids)
spinlock = Threads.SpinLock()

const Torus32 = Int32
const Torus64 = Int64

const parties = 2
const WIDTH = 8

function VolumeMatch(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1},
                    ord::EncOrders, resOrd::EncOrders,
                    accBuy::Vector{MKLweSample}, accSell::Vector{MKLweSample},
                    zero_arr::Vector{MKLweSample}, one_arr::Vector{MKLweSample},
                    one::MKLweSample, zero::MKLweSample, WIDTH, secret_keys::Array{SecretKey_3gen, 1})

    println("accBuy: ", mk_int_decrypt_3gen(secret_keys, accBuy, WIDTH))
    println("accSell: ", mk_int_decrypt_3gen(secret_keys, accSell, WIDTH))

    res_buy = []
    push!(res_buy, zero_arr)
    # println("res_buy: ", mk_int_decrypt_3gen(secret_keys, res_buy[1], WIDTH))

    res_sell = []
    push!(res_sell, zero_arr)

    t1 = @spawnat proc_ids[1] begin
        for x in ord.buy
            accTmp1 = mk_add_3gen(bk, ks, accBuy, x, zero, WIDTH)
            # println("accTmp1: ", mk_int_decrypt_3gen(secret_keys, accTmp1, WIDTH))
            push!(res_buy, accTmp1)
            
            for i = 1:WIDTH
                accBuy[i] = mk_copy_3gen(accTmp1[i])
            end
        end
        return res_buy
    end

    t2 = @spawnat proc_ids[2] begin
        for x in ord.sell
            accTmp2 = mk_add_3gen(bk, ks, accSell, x, zero, WIDTH)
            push!(res_sell, accTmp2)
            
            for i = 1:WIDTH
                accSell[i] = mk_copy_3gen(accTmp2[i])
            end
        end
        return res_sell
    end

    # Wait for both tasks to complete
    @sync for t in (t1, t2)
        wait(t)
    end

    res_buy = fetch(t1)
    res_sell = fetch(t2)

    accBuy = last(res_buy)
    accSell = last(res_sell)

    for x in res_buy
        println("res_buy: ", mk_int_decrypt_3gen(secret_keys, x, WIDTH))
    end

    for x in res_sell
        println("res_sell: ", mk_int_decrypt_3gen(secret_keys, x, WIDTH))
    end

    println("accBuy: ", mk_int_decrypt_3gen(secret_keys, accBuy, WIDTH))
    println("accSell: ", mk_int_decrypt_3gen(secret_keys, accSell, WIDTH))

    sellGRTbuy = mk_grt_3gen(bk, ks, accSell, accBuy, one, WIDTH)

    total1 = Array{MKLweSample}(undef, WIDTH)
    total2 = Array{MKLweSample}(undef, WIDTH)
    totalTmp = Array{MKLweSample}(undef, WIDTH)

    for i = 1:WIDTH
        total1[i] = mk_gate_mux_3gen(bk, ks, sellGRTbuy, accBuy[i], accSell[i])
        total2[i] = total1[i]
    end

    t3 = @spawnat proc_ids[3] begin
        m = size(ord.buy, 1)
        println("m: ", m)
        buy = []

        @sync for i = 1:m

            @spawnat i+proc_ids[4] begin

                println("res_buy: ", mk_int_decrypt_3gen(secret_keys, res_buy[i], WIDTH))

                total1 = mk_sub_3gen(bk, ks, total1, res_buy[i], one, WIDTH)
                ordLeq = mk_leq_3gen(bk, ks, ord.buy[i], total1, one, WIDTH)
                res = Array{MKLweSample}(undef, WIDTH)

                println("total1: ", mk_int_decrypt_3gen(secret_keys, total1, WIDTH))

                for j = 1:WIDTH
                    res[j] = mk_gate_mux_3gen(bk, ks, ordLeq, ord.buy[i][j], total1[j])
                end

                # println("res by worker: ", proc_ids[3], " is: ", mk_int_decrypt_3gen(secret_keys, res, WIDTH))

                # totalTmp = mk_sub_3gen(bk, ks, total1, res, one, WIDTH)

                # for j = 1:WIDTH
                #     total1[j] = mk_copy_3gen(totalTmp[j])
                # end
                println("res by worker: ", i+proc_ids[4], " is: ", mk_int_decrypt_3gen(secret_keys, res, WIDTH))
                push!(buy, res)
            end
        end
        return buy
    end

    t4 = @spawnat proc_ids[4] begin
        n = size(ord.sell, 1)
        m = size(ord.buy, 1)
        println("n: ", n)
        sell = []

        @sync for i = 1:n

            @spawnat i+m+proc_ids[4] begin

                println("res_sell: ", mk_int_decrypt_3gen(secret_keys, res_sell[i], WIDTH))

                total2 = mk_sub_3gen(bk, ks, total1, res_sell[i], one, WIDTH)
                ordLeq = mk_leq_3gen(bk, ks, ord.sell[i], total2, one, WIDTH)
                res = Array{MKLweSample}(undef, WIDTH)

                # println("total2: ", mk_int_decrypt_3gen(secret_keys, total2, WIDTH))

                for j = 1:WIDTH
                    res[j] = mk_gate_mux_3gen(bk, ks, ordLeq, ord.sell[i][j], total2[j])
                end

                # println("res by worker: ", proc_ids[4], " is: ", mk_int_decrypt_3gen(secret_keys, res, WIDTH))

                # totalTmp = mk_sub_3gen(bk, ks, total2, res, one, WIDTH)

                # for j = 1:WIDTH
                #     total2[j] = mk_copy_3gen(totalTmp[j])
                # end

                println("res by worker: ", i+m+proc_ids[4], " is: ", mk_int_decrypt_3gen(secret_keys, res, WIDTH))

                push!(sell, res)

            end
        end
        return sell
    end

    # Wait for both tasks to complete
    @sync for t in (t3, t4)
        wait(t)
    end

    buy = fetch(t3)
    sell = fetch(t4)

    resOrd.buy = buy
    resOrd.sell = sell
    
end

function gen_pk_3gen(rng, secret_keys, crs)
    
    mu = encode_message(-1, 8)

    params = secret_keys[1].params
    alpha = params.lwe_noise_stddev
    n = params.lwe_size
    public_pool_size = 5

    pkTmp = rand_gaussian_torus32(rng, mu, alpha)
    public_keys = Array{Torus32}(undef, parties)

    for i = 1:parties
        for j = 1:n
            pkTmp += crs[i][j] * secret_keys[i].key.key[j]
        end

        for k = 1:public_pool_size
            choice = rand(Bool)
            if choice
                public_keys[i] += pkTmp
            end
        end
    end

    return public_keys

end

function mk_asym_encrypt_3gen(rng, params, public_key, crs, message::Bool)

    mu = encode_message(message ? 1 : -1, 8)

    lwe_params = lwe_parameters(params)
    alpha = params.lwe_noise_stddev

    a = hcat(crs...)
    b = rand_gaussian_torus32(rng, mu, alpha) + public_key

    MKLweSample(lwe_params, a, b, alpha^2)
end

function mk_asym_int_encrypt_3gen(rng, params, public_key, crs, message::Int)

    enc_arr = Array{MKLweSample}(undef, 0)
    for i=1:WIDTH
        bit = (message & 1 == 1) ? true : false
        println("enc bit: ", bit)
        message = (message >> 1)
        enc_mess = mk_asym_encrypt_3gen(rng, params, public_key, crs, bit)
        push!(enc_arr, enc_mess)

    end

    return enc_arr
end

function gen_ext_cipher(params, public_keys, party_id, ciphertext::MKLweSample)

    lwe_params = lwe_parameters(params)
    
    a = ciphertext.a
    b = ciphertext.b
    alpha = ciphertext.current_variance

    for i = 1:parties
        if i != party_id
            b += public_keys[i]
        end
    end

    MKLweSample(lwe_params, a, b, alpha^2)

end

function gen_ext_cipher_arr(params, public_keys, party_id, ciphertext)

    enc_arr = Array{MKLweSample}(undef, 0)
    for i = 1:WIDTH
        tmp_ciper = gen_ext_cipher(params, public_keys, party_id, ciphertext[i])
        push!(enc_arr, tmp_ciper)
    end
    
    return enc_arr
end

function main()

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

    # println("Generating public key . . . ")

    # crs = [rand_uniform_torus32(rng, params.lwe_size) for i in 1:parties]
    # public_keys = gen_pk_3gen(rng, secret_keys, crs)

    # println(public_keys)

    # for i = 1:10
    #     msg1 = rand(Bool)

    #     cipher = mk_asym_encrypt_3gen(rng, params, public_keys[1], crs, msg1)

    #     ext_cipher = gen_ext_cipher(params, public_keys, 1, cipher)

    #     dec_msg1 = mk_decrypt_3gen(secret_keys, ext_cipher)

    #     println("Original msg: ", msg1, " Decryped msg: ", dec_msg1)
    # end

    # msg2 = 8

    # cipher = mk_asym_int_encrypt_3gen(rng, params, public_keys[1], crs, msg2)

    # ext_cipher = gen_ext_cipher_arr(params, public_keys, 1, cipher)

    # dec_msg2 = mk_int_decrypt_3gen(secret_keys, ext_cipher, WIDTH)

    # println("Original msg: ", msg2, " Decryped msg: ", dec_msg2)
    

    sellOrd = Array{Int}(undef, 0)
    buyOrd = Array{Int}(undef, 0)

    push!(sellOrd, 3)
    push!(sellOrd, 4)
    push!(sellOrd, 5)
    push!(sellOrd, 5)


    push!(buyOrd, 5)
    push!(buyOrd, 2)
    push!(buyOrd, 11)
    push!(buyOrd, 1)

    encBuy = []
    encSell = []

    resOrd = EncOrders(encBuy, encSell)

    for s in sellOrd
        encS = mk_int_encrypt_3gen(rng, secret_keys, s, WIDTH)
        push!(encSell, encS)
    end

    for b in buyOrd
        encB = mk_int_encrypt_3gen(rng, secret_keys, b, WIDTH)
        push!(encBuy, encB)
    end

    ord = EncOrders(encBuy, encSell)

    for x in ord.sell
        println(mk_int_decrypt_3gen(secret_keys, x, WIDTH))
    end

    println()

    for x in ord.buy
        println(mk_int_decrypt_3gen(secret_keys, x, WIDTH))
    end

    zero = mk_encrypt_3gen(rng, secret_keys, false)
    one = mk_encrypt_3gen(rng, secret_keys, true)

    accBuy = mk_int_encrypt_3gen(rng, secret_keys, 0, WIDTH)
    accSell = mk_int_encrypt_3gen(rng, secret_keys, 0, WIDTH)

    zero_arr = mk_int_encrypt_3gen(rng, secret_keys, 0, WIDTH)
    one_arr = mk_int_encrypt_3gen(rng, secret_keys, 1, WIDTH)

    @time VolumeMatch(bk_keys, ks_keys, ord, resOrd, accBuy, accSell, zero_arr, one_arr, one, zero, WIDTH, secret_keys)

    println("Resulting Sell: ")
    for x in resOrd.sell
        println(mk_int_decrypt_3gen(secret_keys, x, WIDTH))
    end

    println()

    for x in resOrd.buy
        println(mk_int_decrypt_3gen(secret_keys, x, WIDTH))
    end

end


main()