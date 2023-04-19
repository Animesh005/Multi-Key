include("../../../src/TFHE.jl")
using Random, Printf
using .TFHE
using DelimitedFiles
using Logging
using Statistics


# Creating the log file that contains error logs
io = open("../../test_results/us_simplified/logs/log_us_simplified_errors_3.log", "w+")
logger = SimpleLogger(io)


function main()

    parties_set=[2,3,4,5,8,16,32,64,128,256] # different number of parties that are tested

    params_set=[mktfhe_parameters_2party_3gen,mktfhe_parameters_3party_3gen,mktfhe_parameters_4party_3gen,mktfhe_parameters_5party_3gen,mktfhe_parameters_8party_3gen,mktfhe_parameters_16party_3gen,mktfhe_parameters_32party_3gen,mktfhe_parameters_64party_3gen,mktfhe_parameters_128party_3gen,mktfhe_parameters_256party_3gen,mktfhe_parameters_512party_3gen]

    number_trials=1000 # nbr of times each combination of parties and params is tested

    bk_size_list=zeros(Float64,length(params_set)) # list of bootstrapping key sizes in bytes
    ksk_size_list=zeros(Float64, length(params_set)) # list of key switching key sizes in bytes

    precomp_time_list=zeros(Float64,length(params_set)) # list precomp times for each set of params
    bootstrap_time_min_list=zeros(Float64, length(params_set)) # list of min values for the time of nand gates for each set of params,  (output everything)
    bootstrap_time_median_list=zeros(Float64, length(params_set)) # list of median values for the time of nand gates for each set of params,  (output everything)

    wrong_phase_after_rounding_positive_results=zeros(Int,length(params_set))
    wrong_phase_after_rounding_negative_results=zeros(Int,length(params_set))

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

        precomp_time_list[k]= @elapsed pubkeys=[PublicKey(rng,rlwe_keys[i],params.gsw_noise_stddev,crp_a,tgsw_parameters(params),1) for i=1:parties] # Generation of the individual public keys.

        precomp_time_list[k]+= @elapsed common_pubkey=CommonPubKey_3gen(pubkeys, params, parties)  #generation of the common public key.

        precomp_time_list[k]+= @elapsed bk_keys = [BootstrapKeyPart_3gen(rng, secret_keys[i].key, params.gsw_noise_stddev,crp_a,
                common_pubkey, tgsw_parameters(params), rlwe_parameters(params),1) for i in 1:parties]

        precomp_time_list[k]+= @elapsed bk_keys=[TransformedBootstrapKeyPart_3gen(bk_keys[i]) for i in 1:parties]

        precomp_time_list[k]+= @elapsed ks_keys = [KeyswitchKey(rng,params.ks_noise_stddev, keyswitch_parameters(params),secret_keys[i].key,rlwe_keys[i]) for i in 1:parties]

        @printf("(3) PRECOMP TIME : %s,\n\n",precomp_time_list[k])

        bk_size_list[k]=trunc(Int,Base.summarysize(bk_keys)/parties)
        ksk_size_list[k]=trunc(Int,Base.summarysize(ks_keys)/parties)

        @printf("(3) BK SIZE : %s, KSK SIZE : %s\n\n",getsize(bk_keys), getsize(ks_keys))

        noise_results=Array{Float64}(undef,number_trials * 2) # array to store noise values
        bootstrap_time=Array{Float64}(undef,number_trials * 2)

        wrong_phase_after_rounding_positive = 0 # when the phase after rounding is >1/4 (wrong phase, correct decryption)
        wrong_phase_after_rounding_negative = 0 # when the phase after rounding is <1/4 (wrong phase, wrong decryption)

        for trial=1:number_trials

            mess1 = true
            mess2 = false
            out = !(mess1 && mess2)

            println(" \n\n (3) Trial $k - $trial: $mess1 NAND $mess2 = $out")

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

            bootstrap_time[trial*2-1] = @elapsed enc_mess1=mk_bootstrap_3gen(bk_keys,ks_keys,encode(1,8),enc_mess1)
            bootstrap_time[trial*2] =   @elapsed enc_mess2=mk_bootstrap_3gen(bk_keys,ks_keys,encode(1,8),enc_mess2)

            println("\n Execution time of Bootstrapping of one encrypted message :",(bootstrap_time[trial*2-1]+bootstrap_time[trial*2])/2)

            phase1_bootstrapped = mk_lwe_phase(enc_mess1,[sk.key for sk in secret_keys])
            noise1_bootstrapped=noise_calc(encode_message(1, 8),phase1_bootstrapped)

            phase2_bootstrapped = mk_lwe_phase(enc_mess2,[sk.key for sk in secret_keys])
            noise2_bootstrapped=noise_calc(encode_message(-1, 8),phase2_bootstrapped)

            println("\n noise of bootstrapped encryption of mess1: $noise1_bootstrapped")
            println(" noise of bootstrapped encryption of mess2: $noise2_bootstrapped")

            noise_results[trial*2-1]=noise1_bootstrapped
            noise_results[trial*2]=noise2_bootstrapped

            # Measure of the phase after rounding :

            println("\n Computation of the NAND gate and rounding (without bootstrapping) ...")

            temp = (mk_lwe_noiseless_trivial(encode_message(1, 8), enc_mess1.params, parties) - enc_mess1 - enc_mess2)

            p_degree = params.rlwe_polynomial_degree

            temp_barb = decode_message(temp.b, p_degree * 2) # we change the message space into [-p_degree,p_degree] (rounding)
            temp_bara = decode_message.(temp.a, p_degree * 2)

            temp_barb = encode_message(Int64(temp_barb), p_degree * 2) # We go back to the original message space
            temp_bara = encode_message.(Int64.(temp_bara), p_degree * 2)

            new_temp=MKLweSample(lwe_parameters(params),temp_bara,temp_barb,0.)

            old_temp_phase= mk_lwe_phase(temp,[sk.key for sk in secret_keys])
            new_temp_phase = mk_lwe_phase(new_temp,[sk.key for sk in secret_keys])

            println("\n\n phase of the ciphertext BEFORE rounding :",Float64(old_temp_phase)/2^32)
            println("phase of the ciphertext AFTER rounding :",Float64(new_temp_phase)/2^32,"\n")

            if (Float64(new_temp_phase)/2^32)<0
                wrong_phase_after_rounding_negative+=1
                with_logger(logger) do
                    @info("The phase of the ciphertext after rounding is lower than 0.0" ,k,params,parties,trial,wrong_phase_after_rounding_positive,wrong_phase_after_rounding_negative,new_temp_phase)
                end
                flush(io)

            elseif (Float64(new_temp_phase)/2^32)>0.250
                wrong_phase_after_rounding_positive+=1
                with_logger(logger) do
                    @info("The phase of the ciphertext after rounding is higher than 1/4." ,k,params,parties,trial,wrong_phase_after_rounding_positive,wrong_phase_after_rounding_negative,new_temp_phase)
                end
                flush(io)
            end


        end

        bootstrap_time_min_list[k]= min(bootstrap_time...)
        bootstrap_time_median_list[k]= median(bootstrap_time)

        println("\n\n number of wrong_decryptions_after_rounding_negative:",wrong_phase_after_rounding_negative)
        println("number of wrong_decryptions_after_rounding_positive:",wrong_phase_after_rounding_positive)
        wrong_phase_after_rounding_positive_results[k]=wrong_phase_after_rounding_positive
        wrong_phase_after_rounding_negative_results[k] = wrong_phase_after_rounding_negative

        with_logger(logger) do
            @info("TOTAL STATS OF THE EXPERIMENT" ,k,params,parties,wrong_phase_after_rounding_positive,wrong_phase_after_rounding_negative)
        end
        flush(io)

        #Contains the noise values after execution of bootstrapping (with fresh encryptions)
        #for the scheme number n executed with k parties with the paramset\_number-th parameter set.
        writedlm("../../test_results/us_simplified/mk-noises__scheme-3_parties-"*string(parties)*"_lambda-100_pi-2_qw-2_sf-4.00.dat", noise_results)

        if beginning==1
            open("../../test_results/us_simplified/mk_bootstrap_time_min_3.dat","w+") do file
                #  contains the minimum time measured to run the bootstrapping gate per parameter set in seconds.
                writedlm(file,bootstrap_time_min_list[beginning:k])
            end

            open("../../test_results/us_simplified/mk_bootstrap_time_median_3.dat","w+") do file
                #  contains the median time measured to run the bootstrapping gate per parameter set in seconds.
                writedlm(file,bootstrap_time_median_list[beginning:k])
            end

            open("../../test_results/us_simplified/precomp_times_3.dat","w+") do file
                # precomputation time per parameter set in seconds.
                writedlm(file,precomp_time_list[beginning:k])
            end

            open("../../test_results/us_simplified/mk_bk_sizes_3.dat","w+") do file
                # contains the mean size of a bootstrapping key measured per parameter set in bytes.
                writedlm(file,bk_size_list[beginning:k])
            end

            open("../../test_results/us_simplified/mk_ksk_sizes_3.dat","w+") do file
                # contains the mean size of a ksk measured per parameter set in bytes.
                writedlm(file,ksk_size_list[beginning:k])
            end

            open("../../test_results/us_simplified/mk-positive_errors_3.dat","w+") do file
                #The count of decryptions that are correct but where the phase of 1/8 - c1 - c2
                #after rounding is higher than 1/4. The results are per parameter set.
                writedlm(file,wrong_phase_after_rounding_positive_results[beginning:k])
            end

            open("../../test_results/us_simplified/mk-negative_errors_3.dat","w+") do file
                #The number of wrong decryptions related to the added phase of 1/8 - c1 - c2 after
                #rounding being lower than 0 leading to wrong decryption although bootstrapping
                #is correct. The results are per parameter set.
                writedlm(file,wrong_phase_after_rounding_negative_results[beginning:k])
            end
        else

            open("../../test_results/us_simplified/mk_bootstrap_time_min_3.dat","a+") do file
                writedlm(file,bootstrap_time_min_list[beginning:k])
            end

            open("../../test_results/us_simplified/mk_bootstrap_time_median_3.dat","a+") do file
                writedlm(file,bootstrap_time_median_list[beginning:k])
            end

            open("../../test_results/us_simplified/precomp_times_3.dat","a+") do file
                writedlm(file,precomp_time_list[beginning:k])
            end

            open("../../test_results/us_simplified/mk_bk_sizes_3.dat","a+") do file
                writedlm(file,bk_size_list[beginning:k])
            end

            open("../../test_results/us_simplified/mk_ksk_sizes_3.dat","a+") do file
                writedlm(file,ksk_size_list[beginning:k])
            end

            open("../../test_results/us_simplified/mk-positive_errors_3.dat","a+") do file
                writedlm(file,wrong_phase_after_rounding_positive_results[beginning:k])
            end

            open("../../test_results/us_simplified/mk-negative_errors_3.dat","a+") do file
                writedlm(file,wrong_phase_after_rounding_negative_results[beginning:k])
            end
        end
    end
end

main()
