include("../../../src/TFHE.jl")
using Random, Printf
using .TFHE
using DelimitedFiles
using Logging
using Statistics

# Creating the log file that contains error logs
io = open("../../test_results/CCS/logs/log_CCS_errors_3.log", "w+")
logger = SimpleLogger(io)

function main()

    parties_set=[2,4,8,16] # different number of parties that are tested
    """ different parameters that are tested"""
    params_set = [mktfhe_parameters_2party,mktfhe_parameters_4party,mktfhe_parameters_8party,mktfhe_parameters_16party]

    bk_size_list=zeros(Float64,length(params_set)) # list of bootstrapping key sizes in bytes
    ksk_size_list=zeros(Float64, length(params_set)) # list of key switching key sizes in bytes

    bootstrap_time_min_list=zeros(Float64, length(params_set)) # list of min values for the time of nand gates for each set of params,  (output everything)
    bootstrap_time_median_list=zeros(Float64, length(params_set)) # list of median values for the time of nand gates for each set of params,  (output everything)

    wrong_phase_after_rounding_positive_results=zeros(Int,length(params_set))
    wrong_phase_after_rounding_negative_results=zeros(Int,length(params_set))

    number_trials=1000 # nbr of times each combination of parties and params is tested

    beginning = 1 # param set with which we start 

    for k=beginning:length(params_set)

        parties=parties_set[k]
        params=params_set[k]

        println("\n\n\n*************EXPERIENCE WITH PARAM SET : ",k," (NUMBER OF PARTIES: ",parties_set[k],")*************\n\n\n")

        rng = MersenneTwister()

        @printf("1st MK-TFHE\n========\n(1) KEY GENERATION ...\n")

        function keygen()
            # Processed on clients' machines
            secret_keys = [SecretKey(rng, params) for _ in 1:parties]

            # Created by the server
            shared_key = SharedKey(rng, params)

            # Processed on clients' machines
            ck_parts = [CloudKeyPart(rng, secret_key, shared_key,1) for secret_key in secret_keys]

            # Processed on the server.
            # `ck_parts` only contain information `public_keys`, `secret_keys` remain secret.
            secret_keys, MKCloudKey(ck_parts, shared_key)
        end

        @time secret_keys, cloud_key = keygen()

        getsize(var) = Base.format_bytes(Base.summarysize(var)/parties)

        @printf("(1) BK SIZE : %s, KSK SIZE : %s\n\n", getsize(cloud_key.bootstrap_key), getsize(cloud_key.keyswitch_key))

        bk_size_list[k]=trunc(Int,Base.summarysize(cloud_key.bootstrap_key)/parties)
        ksk_size_list[k]=trunc(Int,Base.summarysize(cloud_key.keyswitch_key)/parties)

        noise_results=Array{Float64}(undef,number_trials * 2)
        bootstrap_time=Array{Float64}(undef,number_trials * 2)

        wrong_phase_after_rounding_positive = 0 # when the phase after rounding is >1/4 (wrong phase, correct decryption) 
        wrong_phase_after_rounding_negative = 0 # when the phase after rounding is <1/4 (wrong phase, wrong decryption) 

        for trial = 1:number_trials

            mess1 = true
            mess2 = false
            out = !(mess1 && mess2)

            println(" \n\n (1) Trial $k - $trial: $mess1 NAND $mess2 = $out")

            enc_mess1 = mk_encrypt(rng, secret_keys, mess1)
            enc_mess2 = mk_encrypt(rng, secret_keys, mess2)

            dec_mess1 = mk_decrypt(secret_keys, enc_mess1)
            dec_mess2 = mk_decrypt(secret_keys, enc_mess2)

            # Maybe we should remove these assert because it can block the functioning with high value parameters
            @assert mess1 == dec_mess1
            @assert mess2 == dec_mess2

            phase1 = mk_lwe_phase(enc_mess1,[sk.key for sk in secret_keys])
            noise1=noise_calc(encode_message(1, 8),phase1)

            phase2 = mk_lwe_phase(enc_mess2,[sk.key for sk in secret_keys])
            noise2=noise_calc(encode_message(-1, 8),phase2)

            println("\n noise of fresh encryption of mess1: $noise1")
            println(" noise of fresh encryption of mess2: $noise2")

            bootstrap_time[trial*2-1] =  @elapsed enc_mess1=mk_bootstrap(cloud_key.bootstrap_key,cloud_key.keyswitch_key,encode_message(1,8),enc_mess1)
            bootstrap_time[trial*2] = @elapsed enc_mess2=mk_bootstrap(cloud_key.bootstrap_key,cloud_key.keyswitch_key,encode_message(1,8),enc_mess2)

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


            temp = (mk_lwe_noiseless_trivial(encode_message(1, 8), enc_mess1.params, cloud_key.parties) - enc_mess1 - enc_mess2)

            p_degree = params.rlwe_polynomial_degree

            temp_barb = decode_message(temp.b, p_degree * 2) # we change the message space into [-p_degree,p_degree] (rounding)
            temp_bara = decode_message.(temp.a, p_degree * 2)

            temp_barb = encode_message(Int64(temp_barb), p_degree * 2) # We go back to the original message space (converting inputs to Int64 should not be a problem)
            temp_bara = encode_message.(Int64.(temp_bara), p_degree * 2)

            new_temp=MKLweSample(lwe_parameters(params),temp_bara,temp_barb,0.)

            old_temp_phase= mk_lwe_phase(temp,[sk.key for sk in secret_keys])
            new_temp_phase = mk_lwe_phase(new_temp,[sk.key for sk in secret_keys])

            println("\n\n phase of the ciphertext BEFORE rounding :",Float64(old_temp_phase)/2^32)
            println("phase of the ciphertext AFTER rounding :",Float64(new_temp_phase)/2^32,"\n\n")

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
        writedlm("../../test_results/CCS/mk-noises__scheme-1_parties-"*string(parties)*"_lambda-100_pi-2_qw-2_sf-4.00.dat", noise_results)

        if beginning==1

            open("../../test_results/CCS/mk_bootstrap_time_min_1.dat","w+") do file
                #  contains the minimum time measured to run the bootstrapping gate per parameter set in seconds.
                writedlm(file,bootstrap_time_min_list[beginning:k])
            end

            open("../../test_results/CCS/mk_bootstrap_time_median_1.dat","w+") do file
                #  contains the median time measured to run the bootstrapping gate per parameter set in seconds.
                writedlm(file,bootstrap_time_median_list[beginning:k])
            end
    
            open("../../test_results/CCS/mk_bk_sizes_1.dat","w+") do file
                # contains the mean size of a bootstrapping key measured per parameter set in bytes.
                writedlm(file,bk_size_list[beginning:k])
            end
    
            open("../../test_results/CCS/mk_ksk_sizes_1.dat","w+") do file
                # contains the mean size of a ksk measured per parameter set in bytes.
                writedlm(file,ksk_size_list[beginning:k])
            end
    
            open("../../test_results/CCS/mk-positive_errors_1.dat","w+") do file
                #The count of decryptions that are correct but where the phase of 1/8 - c1 - c2 
                #after rounding is higher than 1/4. The results are per parameter set.
                writedlm(file,wrong_phase_after_rounding_positive_results[beginning:k])
            end
    
            open("../../test_results/CCS/mk-negative_errors_1.dat","w+") do file
                #The number of wrong decryptions related to the added phase of 1/8 - c1 - c2 after 
                #rounding being lower than 0 leading to wrong decryption although bootstrapping 
                #is correct. The results are per parameter set.
                writedlm(file,wrong_phase_after_rounding_negative_results[beginning:k])
            end
        else

            open("../../test_results/CCS/mk_bootstrap_time_min_1.dat","a+") do file
                writedlm(file,bootstrap_time_min_list[beginning:k])
            end

            open("../../test_results/CCS/mk_bootstrap_time_median_1.dat","a+") do file
                writedlm(file,bootstrap_time_median_list[beginning:k])
            end

            open("../../test_results/CCS/mk_bk_sizes_1.dat","a+") do file
                writedlm(file,bk_size_list[beginning:k])
            end

            open("../../test_results/CCS/mk_ksk_sizes_1.dat","a+") do file
                writedlm(file,ksk_size_list[beginning:k])
            end

            open("../../test_results/CCS/mk-positive_errors_1.dat","a+") do file
                writedlm(file,wrong_phase_after_rounding_positive_results[beginning:k])
            end

            open("../../test_results/CCS/mk-negative_errors_1.dat","a+") do file
                writedlm(file,wrong_phase_after_rounding_negative_results[beginning:k])
            end
        end
    end
end

main()