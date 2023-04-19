
""" We introduce a new version of the TGSW sample that takes into account our simplifications."""
struct TGswSample_3gen
    tgsw_params :: TGswParams
    rlwe_params :: RLweParams
    part_1 :: Array{TorusPolynomial,1} # array of size decomp_length
    part_2 :: Array{TorusPolynomial,1} # array of size decomp_length
    part_3 :: Array{TorusPolynomial,1} # array of size decomp_length
    part_4 :: Array{TorusPolynomial,1} # array of size decomp_length

    function TGswSample_3gen(tgsw_params::TGswParams, rlwe_params :: RLweParams, part_1 :: Array{T,1},part_2 :: Array{T,1},part_3 :: Array{T,1},part_4 :: CRP_3gen) where T <:TorusPolynomial
        new(tgsw_params,rlwe_params, part_1, part_2, part_3, part_4.a)
    end

    function TGswSample_3gen(tgsw_params::TGswParams, rlwe_params :: RLweParams, part_1 :: Array{T,1},part_2 :: Array{T,1},part_3 :: Array{T,1},part_4 :: Array{T,1}) where T <:TorusPolynomial
        new(tgsw_params,rlwe_params, part_1, part_2, part_3, part_4)
    end


end


struct TransformedTGswSample_3gen
    tgsw_params :: TGswParams
    rlwe_params :: RLweParams
    part_1 :: Array{<:Union{TransformedTorusPolynomial, TransformedTorusPolynomial64},1}
    part_2 :: Array{<:Union{TransformedTorusPolynomial, TransformedTorusPolynomial64},1}
    part_3 :: Array{<:Union{TransformedTorusPolynomial, TransformedTorusPolynomial64},1}
    part_4 :: Array{<:Union{TransformedTorusPolynomial, TransformedTorusPolynomial64},1}

    function TransformedTGswSample_3gen(tgsw_params :: TGswParams, rlwe_params :: RLweParams, part_1 :: Array{TransformedTorusPolynomial,1},part_2 :: Array{TransformedTorusPolynomial,1},part_3 :: Array{TransformedTorusPolynomial,1},part_4 ::Array{TransformedTorusPolynomial,1})
        new(tgsw_params,rlwe_params, part_1, part_2, part_3, part_4)
    end

    function TransformedTGswSample_3gen(tgsw_params :: TGswParams, rlwe_params :: RLweParams, part_1 :: Array{TransformedTorusPolynomial64,1},part_2 :: Array{TransformedTorusPolynomial64,1},part_3 :: Array{TransformedTorusPolynomial64,1},part_4 ::Array{TransformedTorusPolynomial64,1})
        new(tgsw_params,rlwe_params, part_1, part_2, part_3, part_4)
    end

end

function tgsw_encrypt_3gen(rng::AbstractRNG, message::Int32, alpha::Float64,common_pubkey::CommonPubKey_3gen,crp_a::CRP_3gen,negative_random::Bool=true, wo_FFT::Int64 = 0)

    params=common_pubkey.params

    if params.rlwe_is32
        rand_uni = rand_uniform_torus32
        rand_uni_bool = (negative_random == false ? rand_uniform_bool : rand_negative_binary)
        rand_gauss = rand_gaussian_torus32
        zero_torus_poly=zero_torus_polynomial
        zero = Int32(0)
        torus = Torus32
    else
        rand_uni = rand_uniform_torus64
        rand_uni_bool= (negative_random == false ? rand_uniform_bool64 : rand_negative_binary64)
        rand_gauss = rand_gaussian_torus64
        zero_torus_poly=zero_torus64_polynomial
        zero = Int64(0)
        torus = Torus64
    end

    random1=[int_polynomial(rand_uni_bool(rng,params.rlwe_polynomial_degree)) for i in 1:params.gsw_decomp_length]
    random2=[int_polynomial(rand_uni_bool(rng,params.rlwe_polynomial_degree)) for i in 1:params.gsw_decomp_length]

    error_part_1=[torus_polynomial(rand_gauss(rng,zero,params.gsw_noise_stddev,params.rlwe_polynomial_degree)) for i in 1:params.gsw_decomp_length]
    error_part_2=[torus_polynomial(rand_gauss(rng,zero,params.gsw_noise_stddev,params.rlwe_polynomial_degree)) for i in 1:params.gsw_decomp_length]
    error_part_3=[torus_polynomial(rand_gauss(rng,zero,params.gsw_noise_stddev,params.rlwe_polynomial_degree)) for i in 1:params.gsw_decomp_length]
    error_part_4=[torus_polynomial(rand_gauss(rng,zero,params.gsw_noise_stddev,params.rlwe_polynomial_degree)) for i in 1:params.gsw_decomp_length]



    if wo_FFT==0
        transformed_random1= forward_transform.(random1,params.rlwe_is32)
        transformed_random2= forward_transform.(random2,params.rlwe_is32)

        """part_1= inverse_transform.(transformed_random1 .* common_pubkey.transformed_b) .+ (torus(message) .* tgsw_parameters(params).gadget_values) .+ error_part_1
        part_2= inverse_transform.(transformed_random2 .* common_pubkey.transformed_b) .+ error_part_2
        part_3= inverse_transform.(transformed_random2 .* crp_a.transformed_a) .+ (torus(message) .* tgsw_parameters(params).gadget_values) .+ error_part_3
        part_4= inverse_transform.(transformed_random1 .* crp_a.transformed_a) .+ error_part_4"""

        part_1=  transformed_mul.(random1,common_pubkey.b,params.rlwe_is32) .+ (torus(message) .* tgsw_parameters(params).gadget_values) .+ error_part_1
        part_2=  transformed_mul.(random2,common_pubkey.b,params.rlwe_is32) .+ error_part_2
        part_3=  transformed_mul.(random2,crp_a.a,params.rlwe_is32) .+ (torus(message) .* tgsw_parameters(params).gadget_values) .+ error_part_3
        part_4=  transformed_mul.(random1,crp_a.a,params.rlwe_is32) .+ error_part_4
    else 
        part_1= random1 .* common_pubkey.b .+ (torus(message) .* tgsw_parameters(params).gadget_values)  .+ error_part_1
        part_2= random2 .* common_pubkey.b .+ error_part_2
        part_3= random2 .* crp_a.a .+ (torus(message) .* tgsw_parameters(params).gadget_values) .+ error_part_3
        part_4= random1 .* crp_a.a .+ error_part_4

    end
    
    return TGswSample_3gen(tgsw_parameters(common_pubkey.params),rlwe_parameters(common_pubkey.params),part_1,part_2,part_3,part_4)


end

forward_transform(source::TGswSample_3gen) =
    TransformedTGswSample_3gen(source.tgsw_params, source.rlwe_params, forward_transform.(source.part_1,source.rlwe_params.is32),forward_transform.(source.part_2,source.rlwe_params.is32),forward_transform.(source.part_3,source.rlwe_params.is32),forward_transform.(source.part_4,source.rlwe_params.is32))



function tgsw_extern_mul_3gen(accum::RLweSample, gsw::TransformedTGswSample_3gen)
    c0=accum.a[2]
    c1=accum.a[1]

    g_c0=decompose(c0,gsw.tgsw_params)
    g_c1=decompose(c1, gsw.tgsw_params)

    c0_prime= inverse_transform(sum(forward_transform.(g_c0,gsw.rlwe_params.is32) .* gsw.part_1) + sum(forward_transform.(g_c1,gsw.rlwe_params.is32) .* gsw.part_2),gsw.rlwe_params.is32)
    c1_prime= inverse_transform(sum(forward_transform.(g_c0,gsw.rlwe_params.is32) .* gsw.part_4) + sum(forward_transform.(g_c1,gsw.rlwe_params.is32) .* gsw.part_3),gsw.rlwe_params.is32)

    return RLweSample(accum.params, [c1_prime,c0_prime],0.)  # TODO : calculate the variance of the result
end




