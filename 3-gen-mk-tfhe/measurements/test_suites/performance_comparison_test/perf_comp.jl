include("../../../src/TFHE.jl")
using Random, Printf
using .TFHE
using DelimitedFiles
using Logging
using Statistics

# Creating the log file that contains error logs
io = open("../../test_results/performance_comparison/logs/perf_comp_1.log", "w+")
logger = SimpleLogger(io)

function main()
    parties_set=[2,4,8,16] # different number of parties that are tested

    params_3gen=mktfhe_parameters_16party_3gen
    params_KMS=mktfhe_parameters_16party_fast
    params_CCS=mktfhe_parameters_16party


    number_trials=100 # nbr of times each combination of parties and params is tested

    bootstrap_time_min_list_3gen=zeros(Float64, length(parties_set)) # list of min values for the time of nand gates for each set of params,  (output everything)
    bootstrap_time_median_list_3gen=zeros(Float64, length(parties_set)) # list of median values for the time of nand gates for each set of params,  (output everything)

    bootstrap_time_min_list_KMS=zeros(Float64, length(parties_set)) 
    bootstrap_time_median_list_KMS=zeros(Float64, length(parties_set))

    bootstrap_time_min_list_CCS=zeros(Float64, length(parties_set)) 
    bootstrap_time_median_list_CCS=zeros(Float64, length(parties_set))




    beginning = 1 # param set with which we start

    for k=beginning:length(parties_set)
        parties=parties_set[k]

        getsize(var) = Base.format_bytes(Base.summarysize(var)/parties)

        println("\n\n\n*************EXPERIENCE WITH PARAM SET : 1 NUMBER OF PARTIES: ",parties_set[k],"*************\n\n\n")

        rng = MersenneTwister()

        @printf("1st, 2nd, 3rd MK-TFHE\n========\n(3) KEY GENERATION AND PRECOMP ...\n")

        secret_keys_3gen = [SecretKey_3gen(rng, params_3gen) for _ in 1:parties]
        rlwe_keys_3gen = [RLweKey(rng,rlwe_parameters(params_3gen),true) for _ in 1:parties]

        crp_a_3gen = CRP_3gen(rng, tgsw_parameters(params_3gen), rlwe_parameters(params_3gen),true)
        
        pubkeys_3gen=[PublicKey(rng,rlwe_keys_3gen[i],params_3gen.gsw_noise_stddev,crp_a_3gen,tgsw_parameters(params_3gen),0) for i=1:parties] # Generation of the individual public keys.
        
        common_pubkey_3gen=CommonPubKey_3gen(pubkeys_3gen, params_3gen, parties)  #generation of the common public key.

        bk_keys_3gen = [BootstrapKeyPart_3gen(rng, secret_keys_3gen[i].key, params_3gen.gsw_noise_stddev,crp_a_3gen,common_pubkey_3gen, tgsw_parameters(params_3gen), rlwe_parameters(params_3gen),0) for i in 1:parties]

        bk_keys_3gen=[TransformedBootstrapKeyPart_3gen(bk_keys_3gen[i]) for i in 1:parties]
        
        ks_keys_3gen = [KeyswitchKey(rng,params_3gen.ks_noise_stddev, keyswitch_parameters(params_3gen),secret_keys_3gen[i].key,rlwe_keys_3gen[i]) for i in 1:parties]

        function keygen_KMS()
            # Processed on clients' machines
            secret_keys = [SecretKey_new(rng, params_KMS) for _ in 1:parties]
        
            # Created by the server
            shared_key = SharedKey_new(rng, params_KMS)
        
            # Processed on clients' machines
            ck_parts = [CloudKeyPart_new(rng, secret_key, shared_key,0) for secret_key in secret_keys]
        
            # Processed on the server.
            # `ck_parts` only contain information `public_keys`, `secret_keys` remain secret.
            secret_keys, MKCloudKey_new(ck_parts, shared_key)
        end

        secret_keys_KMS, cloud_key_KMS = keygen_KMS()

        function keygen_CCS()
            # Processed on clients' machines
            secret_keys = [SecretKey(rng, params_CCS) for _ in 1:parties]

            # Created by the server
            shared_key = SharedKey(rng, params_CCS)

            # Processed on clients' machines
            ck_parts = [CloudKeyPart(rng, secret_key, shared_key,0) for secret_key in secret_keys]

            # Processed on the server.
            # `ck_parts` only contain information `public_keys`, `secret_keys` remain secret.
            secret_keys, MKCloudKey(ck_parts, shared_key)
        end

        secret_keys_CCS, cloud_key_CCS = keygen_CCS()

        println("PRECOMP FINISHED")


        bootstrap_time_3gen=Array{Float64}(undef,number_trials)
        bootstrap_time_KMS=Array{Float64}(undef,number_trials)
        bootstrap_time_CCS=Array{Float64}(undef,number_trials)

        for trial = 1:number_trials

            println(" \n\nTrial $k - $trial")

            mess = true

            enc_mess_3gen = mk_encrypt_3gen(rng, secret_keys_3gen, mess)
            dec_mess_3gen = mk_decrypt_3gen(secret_keys_3gen, enc_mess_3gen)

            enc_mess_KMS = mk_encrypt_new(rng, secret_keys_KMS, mess)
            dec_mess_KMS = mk_decrypt_new(secret_keys_KMS, enc_mess_KMS)
            
            enc_mess_CCS = mk_encrypt(rng, secret_keys_CCS, mess)
            dec_mess_CCS = mk_decrypt(secret_keys_CCS, enc_mess_CCS)

            @assert mess == dec_mess_3gen
            @assert mess == dec_mess_KMS
            @assert mess == dec_mess_CCS

            encode_3gen = params_3gen.rlwe_is32 ? encode_message : encode_message64
            encode_KMS = params_KMS.rlwe_is32 ? encode_message : encode_message64


            bootstrap_time_3gen[trial] = @elapsed enc_mess_3gen=mk_bootstrap_3gen(bk_keys_3gen, ks_keys_3gen, encode_3gen(1,8), enc_mess_3gen)
            println("\n Bootstrapping time 3gen :",bootstrap_time_3gen[trial])
            bootstrap_time_KMS[trial] =  @elapsed enc_mess_KMS=mk_bootstrap_new(cloud_key_KMS.bootstrap_key, cloud_key_KMS.keyswitch_key, encode_KMS(1,8), enc_mess_KMS,true)
            println("\n Bootstrapping time KMS :",bootstrap_time_KMS[trial])
            bootstrap_time_CCS[trial] =  @elapsed enc_mess_CCS=mk_bootstrap(cloud_key_CCS.bootstrap_key, cloud_key_CCS.keyswitch_key, encode_message(1,8), enc_mess_CCS)
            println("\n Bootstrapping time CCS :",bootstrap_time_CCS[trial])

        end

        bootstrap_time_min_list_3gen[k]= min(bootstrap_time_3gen...)
        bootstrap_time_median_list_3gen[k]= median(bootstrap_time_3gen)

        bootstrap_time_min_list_KMS[k]= min(bootstrap_time_KMS...)
        bootstrap_time_median_list_KMS[k]= median(bootstrap_time_KMS)

        bootstrap_time_min_list_CCS[k]= min(bootstrap_time_CCS...)
        bootstrap_time_median_list_CCS[k]= median(bootstrap_time_CCS)

        if beginning==1

            open("../../test_results/performance_comparison/mk_bootstrap_time_min_perf_3gen.dat","w+") do file
                writedlm(file,bootstrap_time_min_list_3gen[beginning:k])
            end

            open("../../test_results/performance_comparison/mk_bootstrap_time_min_perf_KMS.dat","w+") do file
                writedlm(file,bootstrap_time_min_list_KMS[beginning:k])
            end

            open("../../test_results/performance_comparison/mk_bootstrap_time_min_perf_CCS.dat","w+") do file
                writedlm(file,bootstrap_time_min_list_CCS[beginning:k])
            end

            open("../../test_results/performance_comparison/mk_bootstrap_time_median_perf_3gen.dat","w+") do file
                writedlm(file,bootstrap_time_median_list_3gen[beginning:k])
            end

            open("../../test_results/performance_comparison/mk_bootstrap_time_median_perf_KMS.dat","w+") do file
                writedlm(file,bootstrap_time_median_list_KMS[beginning:k])
            end

            open("../../test_results/performance_comparison/mk_bootstrap_time_median_perf_CCS.dat","w+") do file
                writedlm(file,bootstrap_time_median_list_CCS[beginning:k])
            end

        else

            open("../../test_results/performance_comparison/mk_bootstrap_time_min_perf_3gen.dat","a+") do file
                writedlm(file,bootstrap_time_min_list_3gen[beginning:k])
            end

            open("../../test_results/performance_comparison/mk_bootstrap_time_min_perf_KMS.dat","a+") do file
                writedlm(file,bootstrap_time_min_list_KMS[beginning:k])
            end

            open("../../test_results/performance_comparison/mk_bootstrap_time_min_perf_CCS.dat","a+") do file
                writedlm(file,bootstrap_time_min_list_CCS[beginning:k])
            end

            open("../../test_results/performance_comparison/mk_bootstrap_time_median_perf_3gen.dat","a+") do file
                writedlm(file,bootstrap_time_median_list_3gen[beginning:k])
            end

            open("../../test_results/performance_comparison/mk_bootstrap_time_median_perf_KMS.dat","a+") do file
                writedlm(file,bootstrap_time_median_list_KMS[beginning:k])
            end

            open("../../test_results/performance_comparison/mk_bootstrap_time_median_perf_CCS.dat","a+") do file
                writedlm(file,bootstrap_time_median_list_CCS[beginning:k])
            end
        end
    end
end

main()