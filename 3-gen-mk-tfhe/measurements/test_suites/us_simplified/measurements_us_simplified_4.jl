include("../../../src/TFHE.jl")
using Random, Printf
using .TFHE
using DelimitedFiles
using Logging
using Statistics


# Creating the log file that contains error logs
io = open("../../test_results/us_simplified/logs/log_us_simplified_errors_4.log", "w+")
logger = SimpleLogger(io)


function main()

    parties_set=[2,3,4,5,8,16,32,64,128,256] # different number of parties that are tested

    params_set=[mktfhe_parameters_2party_3gen,mktfhe_parameters_3party_3gen,mktfhe_parameters_4party_3gen,mktfhe_parameters_5party_3gen,mktfhe_parameters_8party_3gen,mktfhe_parameters_16party_3gen,mktfhe_parameters_32party_3gen,mktfhe_parameters_64party_3gen,mktfhe_parameters_128party_3gen,mktfhe_parameters_256party_3gen,mktfhe_parameters_512party_3gen]

    number_trials=1000 # nbr of times each combination of parties and params is tested




    precomp_time_list=zeros(Float64,length(params_set)) # list precomp times for each set of params






    beginning = 1 # param set with which we start

    for k=beginning:length(params_set)

        parties=parties_set[k]
        params=params_set[k]

        getsize(var) = Base.format_bytes(Base.summarysize(var)/parties)

        println("\n\n\n*************EXPERIENCE WITH PARAM SET : ",k," NUMBER OF PARTIES: ",parties_set[k],"*************\n\n\n")

        rng = MersenneTwister()

        @printf("3rd MK-TFHE\n========\n(3) KEY GENERATION AND PRECOMP ...\n")

        secret_keys = [SecretKey_3gen(rng, params) for _ in 1:parties]

        rlwe_keys = [RLweKey(rng,rlwe_parameters(params),true) for _ in 1:parties]

        @printf("\nlwe and rlwe keys are generated\n")

        crp_a = CRP_3gen(rng, tgsw_parameters(params), rlwe_parameters(params),true)

        precomp_time_list[k]= @elapsed pubkeys=[PublicKey(rng,rlwe_keys[i],params.gsw_noise_stddev,crp_a,tgsw_parameters(params),0) for i=1:parties] # Generation of the individual public keys.

        precomp_time_list[k]+= @elapsed common_pubkey=CommonPubKey_3gen(pubkeys, params, parties)  #generation of the common public key.

        precomp_time_list[k]+= @elapsed bk_keys = [BootstrapKeyPart_3gen(rng, secret_keys[i].key, params.gsw_noise_stddev,crp_a,
                common_pubkey, tgsw_parameters(params), rlwe_parameters(params),0) for i in 1:parties]

        precomp_time_list[k]+= @elapsed bk_keys=[TransformedBootstrapKeyPart_3gen(bk_keys[i]) for i in 1:parties]

        precomp_time_list[k]+= @elapsed ks_keys = [KeyswitchKey(rng,params.ks_noise_stddev, keyswitch_parameters(params),secret_keys[i].key,rlwe_keys[i]) for i in 1:parties]

        @printf("(3) PRECOMP TIME : %s,\n\n",precomp_time_list[k])




        @printf("(3) BK SIZE : %s, KSK SIZE : %s\n\n",getsize(bk_keys), getsize(ks_keys))

        noise_results=Array{Float64}(undef,number_trials * 2) # array to store noise values


        wrong_decryption=0


        for trial=1:number_trials

            mess1 = true
            mess2 = false
            out = !(mess1 && mess2)

            println(" \n\n (4) Trial $k - $trial: $mess1 NAND $mess2 = $out")

            enc_mess1 = mk_encrypt_3gen(rng, secret_keys, mess1)
            enc_mess2 = mk_encrypt_3gen(rng, secret_keys, mess2)

            dec_mess1 = mk_decrypt_3gen(secret_keys, enc_mess1)
            dec_mess2 = mk_decrypt_3gen(secret_keys, enc_mess2)

            # Maybe we should remove these assert because it can block the functioning with high value parameters
            @assert mess1 == dec_mess1
            @assert mess2 == dec_mess2

            phase1 = mk_lwe_phase(enc_mess1,[sk.key for sk in secret_keys])
            noise1=noise_calc(encode_message(1, 8),phase1)

            phase2 = mk_lwe_phase(enc_mess2,[sk.key for sk in secret_keys])
            noise2=noise_calc(encode_message(-1, 8),phase2)

            println("\n noise of fresh encryption of mess1: $noise1")
            println(" noise of fresh encryption of mess2: $noise2")

            encode = params.rlwe_is32 ? encode_message : encode_message64

            bootstrap_time =            @elapsed enc_mess1=mk_bootstrap_3gen(bk_keys,ks_keys,encode(1,8),enc_mess1)
            bootstrap_time +=           @elapsed enc_mess2=mk_bootstrap_3gen(bk_keys,ks_keys,encode(1,8),enc_mess2)

            println("\n Execution time of Bootstrapping of one encrypted message :",bootstrap_time/2)

            phase1_bootstrapped = mk_lwe_phase(enc_mess1,[sk.key for sk in secret_keys])
            noise1_bootstrapped=noise_calc(encode_message(1, 8),phase1_bootstrapped)

            phase2_bootstrapped = mk_lwe_phase(enc_mess2,[sk.key for sk in secret_keys])
            noise2_bootstrapped=noise_calc(encode_message(-1, 8),phase2_bootstrapped)

            println("\n noise of bootstrapped encryption of mess1: $noise1_bootstrapped")
            println(" noise of bootstrapped encryption of mess2: $noise2_bootstrapped")

            noise_results[trial*2-1]=noise1_bootstrapped
            noise_results[trial*2]=noise2_bootstrapped

            # Measure of the phase after rounding :
            #
            # --- none ---



















            if (Float64(phase1_bootstrapped)/2^32)<0 || (Float64(phase1_bootstrapped)/2^32)>0.250
                wrong_decryption+=1
                with_logger(logger) do
                    @info("wrong_decryption" ,k,params,parties,trial,wrong_decryption,out,encode_message(1, 8),phase1_bootstrapped,noise1_bootstrapped)
                end
                flush(io)
            end

            if (Float64(phase2_bootstrapped)/2^32)<(-0.250) || (Float64(phase2_bootstrapped)/2^32)>0
                wrong_decryption+=1
                with_logger(logger) do
                    @info("wrong_decryption" ,k,params,parties,trial,wrong_decryption,out,encode_message(-1, 8),phase2_bootstrapped,noise2_bootstrapped)
                end
                flush(io)
            end
        end

        #Contains the noise values after execution of bootstrapping (with fresh encryptions)
        #for the scheme number n executed with k parties with the paramset\_number-th parameter set WITH FFT DURING PRECOMP.
        writedlm("../../test_results/us_simplified/mk-noises__scheme-3_parties-"*string(parties)*"_lambda-100_pi-2_qw-2_sf-4.00_w_FFT.dat", noise_results)

        if beginning==1
            open("../../test_results/us_simplified/precomp_times_3_w_FFT.dat","w+") do file
                # # precomputation time per parameter set in seconds  WITH FFT DURING PRECOMP.
                writedlm(file,precomp_time_list[beginning:k])
            end
        else
            open("../../test_results/us_simplified/precomp_times_3_w_FFT.dat","a+") do file
                writedlm(file,precomp_time_list[beginning:k])
            end
        end
    end
end

main()


