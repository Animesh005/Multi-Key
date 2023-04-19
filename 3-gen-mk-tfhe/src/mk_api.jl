"""
Multi-key TFHE parameters for 2 parties (a [`SchemeParameters`](@ref) object).
"""
mktfhe_parameters_2party = SchemeParameters(
    560, 3.05e-5, # LWE parameters
    1024, 1, true, # RLWE parameters
    3, 9, 3.72e-9, # bootstrap parameters
    8, 2, 3.05e-5, # keyswitch parameters
    2
    )

mktfhe_parameters_2party_new = SchemeParameters_new(
    560, 3.05e-5, # LWE parameters
    2048, 1, false, # RLWE parameters
    3, 13, 4.63e-18, # gsw parameters
    2, 7, # lev parameters
    2, 13, 4.63e-18, # unienc parameters
    8, 2, 3.05e-5, # keyswitch parameters
    2
    )

mktfhe_parameters_2party_fast = SchemeParameters_new(
    560, 3.05e-5, # LWE parameters
    2048, 1, false, # RLWE parameters
    3, 13, 4.63e-18, # gsw parameters
    2, 7, # lev parameters
    3, 10, 4.63e-18, # unienc parameters
    8, 2, 3.05e-5, # keyswitch parameters
    2
    )

mktfhe_parameters_2party_3gen = SchemeParameters_3gen(
    520, 2^(-13.52), # LWE parameters
    1024, 1, false, # RLWE parameters
    2, 7, 2^(-30.70), # gsw parameters
    3, 3, 2^(-13.52), # keyswitch parameters
    2
    )

"""
Multi-key TFHE parameters for 3 parties (a [`SchemeParameters`](@ref) object).
"""

mktfhe_parameters_3party_3gen = SchemeParameters_3gen(
    510, 2^(-13.26), # LWE parameters
    1024, 1, false,# RLWE parameters
    2, 7, 2^(-30.70), # bootstrap parameters
    5, 2,2^(-13.26) , # keyswitch parameters
    3
    )


"""
Multi-key TFHE parameters for 4 parties (a [`SchemeParameters`](@ref) object).
"""
mktfhe_parameters_4party = SchemeParameters(
    560, 3.05e-5, # LWE parameters
    1024, 1, true,# RLWE parameters
    4, 8, 3.72e-9, # bootstrap parameters
    8, 2, 3.05e-5, # keyswitch parameters
    4
    )

mktfhe_parameters_4party_new = SchemeParameters_new(
    560, 3.05e-5, # LWE parameters
    2048, 1, false, # RLWE parameters
    5, 8, 4.63e-18, # gsw parameters #37
    2, 8, # lev parameters
    5, 8, 4.63e-18, # unienc parameters
    8, 2, 3.05e-5, # keyswitch parameters
    4
    )

mktfhe_parameters_4party_fast = SchemeParameters_new(
    560, 3.05e-5, # LWE parameters
    2048, 1, false, # RLWE parameters
    5, 8, 4.63e-18, # gsw parameters #37
    2, 8, # lev parameters
    7, 6, 4.63e-18, # unienc parameters
    8, 2, 3.05e-5, # keyswitch parameters
    4
    )

mktfhe_parameters_4party_3gen = SchemeParameters_3gen(
    510, 2^(-13.26), # LWE parameters
    1024, 1, false,# RLWE parameters
    3, 6, 2^(-30.70), # bootstrap parameters
    5, 2,2^(-13.26) , # keyswitch parameters
    4
    )


"""
Multi-key TFHE parameters for 5 parties (a [`SchemeParameters`](@ref) object).
"""


mktfhe_parameters_5party_3gen = SchemeParameters_3gen(
    520, 2^(-13.52), # LWE parameters
    1024, 1, false,# RLWE parameters
    3, 6, 2^(-30.70), # bootstrap parameters
    5, 2,2^(-13.52) , # keyswitch parameters
    5
    )



"""
Multi-key TFHE parameters for 8 parties (a [`SchemeParameters`](@ref) object).
"""
mktfhe_parameters_8party = SchemeParameters(
    560, 3.05e-5, # LWE parameters
    1024, 1, true,# RLWE parameters
    5, 6, 3.72e-9, # bootstrap parameters
    8, 2, 3.05e-5, # keyswitch parameters
    8
    )


mktfhe_parameters_8party_new = SchemeParameters_new(
    560, 3.05e-5, # LWE parameters
    2048, 1, false, # RLWE parameters
    4, 11, 4.63e-18, # gsw parameters
    3, 6, # lev parameters
    8, 4, 4.63e-18, # unienc parameters
    8, 2, 3.05e-5, # keyswitch parameters
    8
    )

mktfhe_parameters_8party_fast = SchemeParameters_new(
    560, 3.05e-5, # LWE parameters
    2048, 1, false, # RLWE parameters
    4, 11, 4.63e-18, # gsw parameters
    3, 6, # lev parameters
    7, 4, 4.63e-18, # unienc parameters
    8, 2, 3.05e-5, # keyswitch parameters
    8
    )

mktfhe_parameters_8party_3gen = SchemeParameters_3gen(   # variant A
    540, 2^(-14.04), # LWE parameters
    1024, 1, false,# RLWE parameters
    4, 4, 2^(-30.70), # bootstrap parameters
    5, 2,2^(-14.04) , # keyswitch parameters
    8
    )

#~ mktfhe_parameters_8party_3gen = SchemeParameters_3gen(   # variant B
#~     540, 2^(-14.04), # LWE parameters
#~     1024, 1, false,# RLWE parameters
#~     4, 4, 2^(-30.70), # bootstrap parameters
#~     6, 2,2^(-14.04) , # keyswitch parameters
#~     8
#~     )

#~ mktfhe_parameters_8party_3gen = SchemeParameters_3gen(   # variant C
#~     550, 2^(-14.30), # LWE parameters
#~     1024, 1, false,# RLWE parameters
#~     4, 4, 2^(-30.70), # bootstrap parameters
#~     6, 2,2^(-14.04) , # keyswitch parameters
#~     8
#~     )

#~ mktfhe_parameters_8party_3gen = SchemeParameters_3gen(   # variant D
#~     560, 2^(-14.56), # LWE parameters
#~     1024, 1, false,# RLWE parameters
#~     4, 4, 2^(-30.70), # bootstrap parameters
#~     6, 2,2^(-14.04) , # keyswitch parameters
#~     8
#~     )

    #~ mktfhe_parameters_8party_3gen = SchemeParameters_3gen(   # variant WTF
    #~     570, 2^(-14.82), # LWE parameters
    #~     1024, 1, false,# RLWE parameters
    #~     4, 4, 2^(-30.70), # bootstrap parameters
    #~     6, 2,2^(-14.82) , # keyswitch parameters
    #~     8
    #~     )



"""
Multi-key TFHE parameters for 16 parties (a [`SchemeParameters`](@ref) object).
"""
mktfhe_parameters_16party = SchemeParameters(
    560, 3.05e-5, # LWE parameters
    1024, 1, true,# RLWE parameters
    12, 2, 3.72e-9, # bootstrap parameters
    8, 2, 3.05e-5, # keyswitch parameters
    16
    )


mktfhe_parameters_16party_new = SchemeParameters_new(
    560, 3.05e-5, # LWE parameters
    2048, 1, false, # RLWE parameters
    5, 9, 4.63e-18, # gsw parameters
    3, 6, # lev parameters
    9, 4, 4.63e-18, # unienc parameters
    8, 2, 3.05e-5, # keyswitch parameters
    16
    )

mktfhe_parameters_16party_fast = SchemeParameters_new(
    560, 3.05e-5, # LWE parameters
    2048, 1, false, # RLWE parameters
    5, 9, 4.63e-18, # gsw parameters
    3, 6, # lev parameters
    7, 4, 4.63e-18, # unienc parameters
    8, 2, 3.05e-5, # keyswitch parameters
    16
    )

mktfhe_parameters_16party_3gen = SchemeParameters_3gen(
    590, 2^(-15.34), # LWE parameters
    2048, 1, false,# RLWE parameters
    1, 26, 2^(-62.00), # bootstrap parameters
    4, 3,2^(-15.34) , # keyswitch parameters
    16
    )

"""
Multi-key TFHE parameters for 32 parties (a [`SchemeParameters`](@ref) object).
"""
mktfhe_parameters_32party_new = SchemeParameters_new(
    560, 3.05e-5, # LWE parameters
    2048, 1, false, # RLWE parameters
    6, 8, 4.63e-18, # gsw parameters
    3, 7, # lev parameters
    16, 2, 4.63e-18, # unienc parameters
    8, 2, 3.05e-5, # keyswitch parameters
    32
    )

mktfhe_parameters_32party_fast = SchemeParameters_new(
    560, 3.05e-5, # LWE parameters
    2048, 1, false, # RLWE parameters
    6, 8, 4.63e-18, # gsw parameters
    3, 7, # lev parameters
    16, 2, 4.63e-18, # unienc parameters
    8, 2, 3.05e-5, # keyswitch parameters
    32
    )


mktfhe_parameters_32party_3gen = SchemeParameters_3gen(
    620, 2^(-16.12), # LWE parameters
    2048, 1, false,# RLWE parameters
    1, 26, 2^(-62.00), # bootstrap parameters
    4, 3,2^(-16.12) , # keyswitch parameters
    32
    )

"""9 sigma"""
mktfhe_parameters_32party_3gen_for_fft = SchemeParameters_3gen(
    680, 2^(-17.68), # LWE parameters
    2048, 1, false,# RLWE parameters
    1, 25, 2^(-62.00), # bootstrap parameters
    5, 3,2^(-17.68) , # keyswitch parameters
    32
)

"""
Multi-key TFHE parameters for 64 parties (a [`SchemeParameters`](@ref) object).
"""


mktfhe_parameters_64party_3gen = SchemeParameters_3gen(
    650, 2^(-16.90), # LWE parameters
    2048, 1, false,# RLWE parameters
    1, 25, 2^(-62.00), # bootstrap parameters
    4, 3,2^(-16.90) , # keyswitch parameters
    64
)

"""9 sigma"""
mktfhe_parameters_64party_3gen_for_fft = SchemeParameters_3gen(
    720, 2^(-18.72), # LWE parameters
    4096, 1, false,# RLWE parameters
    1, 27, 2^(-62.00), # bootstrap parameters
    5, 3,2^(-18.72) , # keyswitch parameters
    64
)




"""
Multi-key TFHE parameters for 128 parties (a [`SchemeParameters`](@ref) object).
"""

mktfhe_parameters_128party_3gen = SchemeParameters_3gen(
    670, 2^(-17.42), # LWE parameters
    2048, 1, false,# RLWE parameters
    1, 24, 2^(-62.00), # bootstrap parameters
    5, 3,2^(-17.42) , # keyswitch parameters
    128
    )

"""
Multi-key TFHE parameters for 256 parties (a [`SchemeParameters`](@ref) object).
"""

mktfhe_parameters_256party_3gen = SchemeParameters_3gen(
    740, 2^(-19.24), # LWE parameters
    2048, 1, false,# RLWE parameters
    2, 18, 2^(-62.00), # bootstrap parameters
    8, 2,2^(-19.24) , # keyswitch parameters
    256
    )

"""
Multi-key TFHE parameters for 512 parties (a [`SchemeParameters`](@ref) object).
"""

mktfhe_parameters_512party_3gen = SchemeParameters_3gen(
    730, 2^(-18.98), # LWE parameters
    4096, 1, false,# RLWE parameters
    1, 27, 2^(-62.00), # bootstrap parameters
    5, 3,2^(-18.98) , # keyswitch parameters
    512
    )



"""
    SharedKey(rng::AbstractRNG, params::SchemeParameters)

A shared key created by the server.
`params` is one of [`mktfhe_parameters_2party`](@ref), [`mktfhe_parameters_4party`](@ref),
[`mktfhe_parameters_8party`](@ref).
"""
function SharedKey(rng::AbstractRNG, params::SchemeParameters)
    # Resolving a circular dependency. SharedKey is used internally,
    # and we don't want to expose SchemeParameters there.
    tgsw_params = tgsw_parameters(params)
    rlwe_params = rlwe_parameters(params)
    SharedKey(rng, tgsw_params, rlwe_params)
end

function SharedKey_new(rng::AbstractRNG, params::SchemeParameters_new)
    # Resolving a circular dependency. SharedKey is used internally,
    # and we don't want to expose SchemeParameters there.
    uni_params = uni_parameters(params)
    rlwe_params = rlwe_parameters(params)
    SharedKey(rng, uni_params, rlwe_params)
end

"""
Function to generate a common random polynomial.
@info :In 3rd Gen MKTHFE, we don't use the structure of SharedKey but of CRP because the SharedKey name can be confusing.
"""
function GenCRP_3gen(rng::AbstractRNG, params::SchemeParameters_3gen, a_same::Bool = false)
    tgsw_params = tgsw_parameters(params)
    rlwe_params = rlwe_parameters(params)
    CRP_3gen(rng, tgsw_params, rlwe_params,a_same) # in mk_internals
end

"""
    CloudKeyPart(rng, secret_key::SecretKey, shared_key::SharedKey)

A part of the cloud (computation) key generated independently by each party
(since it involves their secret keys).
The `secret_key` is a [`SecretKey`](@ref) object created with the same parameter set
as the [`SharedKey`](@ref) object.
"""

struct CloudKeyPart
    params :: SchemeParameters
    bk_part :: BootstrapKeyPart
    ks :: KeyswitchKey

    function CloudKeyPart(rng, secret_key::SecretKey, shared_key::SharedKey,wo_FFT::Int64 = 0)
        params = secret_key.params
        tgsw_params = tgsw_parameters(params)
        rlwe_key = RLweKey(rng, rlwe_parameters(params))
        pk = PublicKey(rng, rlwe_key, params.bs_noise_stddev, shared_key, tgsw_params, wo_FFT)
        bk = BootstrapKeyPart(rng, secret_key.key, rlwe_key, params.bs_noise_stddev, shared_key, pk, wo_FFT)
        ks = KeyswitchKey(
                rng, params.ks_noise_stddev, keyswitch_parameters(params),
                secret_key.key, rlwe_key)
        new(params, bk, ks)
    end
end


"""
    MKCloudKey(ck_parts::Array{CloudKeyPart, 1})

A full cloud key generated on the server out of parties' cloud key parts.
"""
struct MKCloudKey
    parties :: Int
    params :: SchemeParameters
    bootstrap_key :: MKBootstrapKey
    keyswitch_key :: Array{KeyswitchKey, 1}

    function MKCloudKey(ck_parts::Array{CloudKeyPart, 1}, shared_key::SharedKey)
        params = ck_parts[1].params
        parties = length(ck_parts)
        @assert parties <= params.max_parties

        bk = MKBootstrapKey([part.bk_part for part in ck_parts], shared_key)
        ks = [part.ks for part in ck_parts]

        new(parties, params, bk, ks)
    end
end

"""
New.
"""
struct CloudKeyPart_new
    params :: SchemeParameters_new
    bk_part :: BootstrapKeyPart_new
    ks :: KeyswitchKey

    function CloudKeyPart_new(rng, secret_key::SecretKey_new, shared_key::SharedKey,wo_FFT::Int64=0)
        params = secret_key.params
        uni_params = uni_parameters(params)
        tlev_params = tlev_parameters(params)
        tgsw_params = tgsw_parameters(params)

        rlwe_key = RLweKey(rng, rlwe_parameters(params))

        pk = PublicKey(rng, rlwe_key, params.uni_noise_stddev, shared_key, uni_params,wo_FFT)
        bk = BootstrapKeyPart_new(rng, secret_key.key, rlwe_key, params.gsw_noise_stddev, params.uni_noise_stddev,
                shared_key, pk, uni_params, tlev_params, tgsw_params,wo_FFT)
        ks = KeyswitchKey(
                rng, params.ks_noise_stddev, keyswitch_parameters(params),
                secret_key.key, rlwe_key)

        new(params, bk, ks)
    end
end

"""
New.
"""
struct MKCloudKey_new
    parties :: Int
    params :: SchemeParameters_new
    bootstrap_key :: MKBootstrapKey_new
    keyswitch_key :: Array{KeyswitchKey, 1}

    function MKCloudKey_new(ck_parts::Array{CloudKeyPart_new, 1}, shared_key::SharedKey)
        params = ck_parts[1].params
        parties = length(ck_parts)
        @assert parties <= params.max_parties

        bk = MKBootstrapKey_new([part.bk_part for part in ck_parts], shared_key)
        ks = [part.ks for part in ck_parts]

        new(parties, params, bk, ks)
    end
end

struct MKCloudKey_new_wo_FFT
    parties :: Int
    params :: SchemeParameters_new
    bootstrap_key :: MKBootstrapKey_new_wo_FFT
    keyswitch_key :: Array{KeyswitchKey, 1}

    function MKCloudKey_new_wo_FFT(ck_parts::Array{CloudKeyPart_new, 1}, shared_key::SharedKey)
        params = ck_parts[1].params
        parties = length(ck_parts)
        @assert parties <= params.max_parties

        bk = MKBootstrapKey_new_wo_FFT([part.bk_part for part in ck_parts], shared_key)
        ks = [part.ks for part in ck_parts]

        new(parties, params, bk, ks)
    end
end


"""
    mk_encrypt(rng, secret_keys::Array{SecretKey, 1}, message::Bool)

Encrypts a plaintext bit using parties' secret keys.
Returns a [`MKLweSample`](@ref) object.
"""
function mk_encrypt(rng, secret_keys::Array{SecretKey, 1}, message::Bool)

    # TODO: (issue #6) encrypt separately for each party and share <a_i, s_i>?

    mu = encode_message(message ? 1 : -1, 8)

    params = secret_keys[1].params
    lwe_params = lwe_parameters(params)
    alpha = params.lwe_noise_stddev
    parties = length(secret_keys)

    a = hcat([rand_uniform_torus32(rng, lwe_params.size) for i in 1:parties]...)
    b = (rand_gaussian_torus32(rng, mu, alpha)
        + reduce(+, a .* hcat([secret_keys[i].key.key for i in 1:parties]...)))

    MKLweSample(lwe_params, a, b, alpha^2)
end

function mk_encrypt_new(rng, secret_keys::Array{SecretKey_new, 1}, message::Bool)

    # TODO: (issue #6) encrypt separately for each party and share <a_i, s_i>?

    mu = encode_message(message ? 1 : -1, 8)

    params = secret_keys[1].params
    lwe_params = lwe_parameters(params)
    alpha = params.lwe_noise_stddev
    parties = length(secret_keys)

    a = hcat([rand_uniform_torus32(rng, lwe_params.size) for i in 1:parties]...)
    b = (rand_gaussian_torus32(rng, mu, alpha)
        + reduce(+, a .* hcat([secret_keys[i].key.key for i in 1:parties]...)))

    MKLweSample(lwe_params, a, b, alpha^2)
end

function mk_encrypt_3gen(rng, secret_keys::Array{SecretKey_3gen, 1}, message::Bool)

    # TODO: (issue #6) encrypt separately for each party and share <a_i, s_i>?

    
    mu = encode_message(message ? 1 : -1, 8)

    params = secret_keys[1].params
    lwe_params = lwe_parameters(params)
    alpha = params.lwe_noise_stddev
    parties = length(secret_keys)

    a = hcat([rand_uniform_torus32(rng, lwe_params.size) for i in 1:parties]...)
    b = (rand_gaussian_torus32(rng, mu, alpha)
        + reduce(+, a .* hcat([secret_keys[i].key.key for i in 1:parties]...)))

    MKLweSample(lwe_params, a, b, alpha^2)
end

# function mk_encrypt_3gen_gpu(rng, secret_keys::CuArray{SecretKey_3gen, 1}, message::Bool)

#     # TODO: (issue #6) encrypt separately for each party and share <a_i, s_i>?

    
#     mu = encode_message(message ? 1 : -1, 8)

#     params = secret_keys[1].params
#     lwe_params = lwe_parameters(params)
#     alpha = params.lwe_noise_stddev
#     parties = length(secret_keys)

#     a = hcat([rand_uniform_torus32(rng, lwe_params.size) for i in 1:parties]...)
#     b = (rand_gaussian_torus32(rng, mu, alpha)
#         + reduce(+, a .* hcat([secret_keys[i].key.key for i in 1:parties]...)))

#     MKLweSampleGPU(lwe_params, a, b, alpha^2)
# end

# function mk_encrypt_3gen(rng, secret_keys::Array{SecretKey_3gen, 1}, message)

#     # TODO: (issue #6) encrypt separately for each party and share <a_i, s_i>?

    
#     mu = encode_message((message == 1) ? 1 : -1, 8)

#     params = secret_keys[1].params
#     lwe_params = lwe_parameters(params)
#     alpha = params.lwe_noise_stddev
#     parties = length(secret_keys)

#     a = hcat([rand_uniform_torus32(rng, lwe_params.size) for i in 1:parties]...)
#     b = (rand_gaussian_torus32(rng, mu, alpha)
#         + reduce(+, a .* hcat([secret_keys[i].key.key for i in 1:parties]...)))

#     MKLweSample(lwe_params, a, b, alpha^2)
# end

function mk_int_encrypt_3gen(rng, secret_keys::Array{SecretKey_3gen, 1}, message::Int, WIDTH)

    enc_arr = Array{MKLweSample}(undef, 0)
    for i=1:WIDTH
        bit = (message & 1 == 1) ? true : false
        message = (message >> 1)
        enc_mess = mk_encrypt_3gen(rng, secret_keys, bit)
        push!(enc_arr, enc_mess)

    end

    return enc_arr

end

"""
    mk_decrypt(secret_keys::Array{SecretKey, 1}, sample::MKLweSample)

Decrypts an encrypted bit using parties' secret keys.
Returns a boolean.
"""
function mk_decrypt(secret_keys::Array{SecretKey, 1}, sample::MKLweSample)
    # TODO: (issue #6) decrypt separately at each party and join phases?
    mk_lwe_phase(sample, [sk.key for sk in secret_keys]) > 0
end

function mk_decrypt_new(secret_keys::Array{SecretKey_new, 1}, sample::MKLweSample)
    # TODO: (issue #6) decrypt separately at each party and join phases?
    mk_lwe_phase(sample, [sk.key for sk in secret_keys]) > 0
end

function mk_decrypt_3gen(secret_keys::Array{SecretKey_3gen, 1}, sample::MKLweSample)
    # TODO: (issue #6) decrypt separately at each party and join phases? + This decryption only works for booleans.
    mk_lwe_phase(sample, [sk.key for sk in secret_keys]) > 0
end

function mk_int_decrypt_3gen(secret_keys::Array{SecretKey_3gen, 1}, sample::Vector{MKLweSample}, WIDTH)

    msb = mk_decrypt_3gen(secret_keys, sample[WIDTH])
    # println("msb: ", msb)

    result = 0

    for i=1:WIDTH-1
        bit = mk_decrypt_3gen(secret_keys, sample[i])
        # println("bit: ", bit)
        temp = xor(bit, msb) << (i-1)
        result += temp
    end

    if msb == true
        result = result + 1
        result = -result
    end

    return result

end
