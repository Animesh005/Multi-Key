struct RLweParams
    polynomial_degree :: Int # a power of 2: degree of the polynomials
    mask_size :: Int # number of polynomials in the mask

    is32 :: Bool

    function RLweParams(polynomial_degree::Int, mask_size::Int, is32::Bool)
        new(polynomial_degree, mask_size, is32)
    end
end


struct RLweKey
    params :: RLweParams
    key :: Array{IntPolynomial, 1} # the key (i.e k binary polynomials)

    function RLweKey(rng::AbstractRNG, params::RLweParams,negative::Bool=false)
        if negative==false
            key = params.is32 ?
                [int_polynomial(rand_uniform_bool(rng, params.polynomial_degree)) for i in 1:params.mask_size] :
                [int_polynomial(rand_uniform_bool64(rng, params.polynomial_degree)) for i in 1:params.mask_size]
            new(params, key)
        else
            key = params.is32 ?
                [int_polynomial(rand_negative_binary(rng, params.polynomial_degree)) for i in 1:params.mask_size] :
                [int_polynomial(rand_negative_binary64(rng, params.polynomial_degree)) for i in 1:params.mask_size]
            new(params, key)
        end
    end
end


# extractions Ring Lwe . Lwe
function extract_lwe_key(rlwe_key::RLweKey)
    rlwe_params = rlwe_key.params

    key = Int32.(vcat([poly.coeffs for poly in rlwe_key.key]...))

    LweKey(LweParams(rlwe_params.polynomial_degree * rlwe_params.mask_size), key)
end


struct RLweSample
    params :: RLweParams
    a :: Array{TorusPolynomial, 1} # array of length mask_size+1: mask + right term
    current_variance :: Float64 # avg variance of the sample

    RLweSample(params::RLweParams, a::Array{T, 1}, cv::Float64) where T <: TorusPolynomial =
        new(params, a, cv)
end


struct TransformedRLweSample
    params :: RLweParams
    a :: Array{<:Union{TransformedTorusPolynomial, TransformedTorusPolynomial64}, 1} # array of length mask_size+1: mask + right term
    current_variance :: Float64 # avg variance of the sample

    TransformedRLweSample(
            params::RLweParams, a::Array{<:Union{TransformedTorusPolynomial, TransformedTorusPolynomial64}, 1}, cv::Float64) =
        new(params, a, cv)
end


function rlwe_extract_sample(x::RLweSample)
    a = vcat([reverse_polynomial(p).coeffs for p in x.a[1:end-1]]...)
    b = x.a[end].coeffs[1]
    LweSample(LweParams(length(a)), a, b, 0.) # TODO: (issue #7) calculate the current variance
end

function rlwe_extract_sample_64(x::RLweSample)
    a = t64tot32.(vcat([reverse_polynomial(p).coeffs for p in x.a[1:end-1]]...))
    b = t64tot32(x.a[end].coeffs[1])
    LweSample(LweParams(length(a)), a, b, 0.) # TODO: (issue #7) calculate the current variance
end



# create a homogeneous RLWE sample
function rlwe_encrypt_zero(rng::AbstractRNG, alpha::Float64, key::RLweKey,wo_FFT::Int64 = 0)
    params = key.params
    polynomial_degree = params.polynomial_degree
    mask_size = params.mask_size

    if params.is32
        rand_uni = rand_uniform_torus32
        rand_gauss = rand_gaussian_torus32
        zero = Int32(0)
    else
        rand_uni = rand_uniform_torus64
        rand_gauss = rand_gaussian_torus64
        zero = Int64(0)
    end

    a_part = [torus_polynomial(rand_uni(rng, polynomial_degree)) for i in 1:mask_size]

    if wo_FFT==0
        a_last = (
            int_polynomial(rand_gauss(rng, zero, alpha, polynomial_degree))
            + sum(transformed_mul.(key.key, a_part, params.is32)))
    else
        a_last = (
            int_polynomial(rand_gauss(rng, zero, alpha, polynomial_degree))
            + sum(key.key .* a_part))
    end

    RLweSample(params, vcat(a_part, [a_last]), alpha^2)
end




# result = (0,mu)
function rlwe_noiseless_trivial(mu::TorusPolynomial, params::RLweParams)
    a_part = params.is32 ?
        [zero_torus_polynomial(params.polynomial_degree) for i in 1:params.mask_size] :
        [zero_torus64_polynomial(params.polynomial_degree) for i in 1:params.mask_size]
    a_last = deepcopy(mu)
    RLweSample(params, vcat(a_part, [a_last]), 0.)
end


Base.:+(x::RLweSample, y::RLweSample) =
    RLweSample(x.params, x.a .+ y.a, x.current_variance + y.current_variance)


Base.:-(x::RLweSample, y::RLweSample) =
    RLweSample(x.params, x.a .- y.a, x.current_variance + y.current_variance)


mul_by_monomial(x::RLweSample, shift::Integer) =
    RLweSample(x.params, mul_by_monomial.(x.a, shift), x.current_variance)


forward_transform(x::RLweSample) =
    TransformedRLweSample(x.params, forward_transform.(x.a, x.params.is32), x.current_variance)


inverse_transform(x::TransformedRLweSample) =
    RLweSample(x.params, inverse_transform.(x.a, x.params.is32), x.current_variance)


# TODO: (issue #7) how to compute the variance correctly?
Base.:+(x::TransformedRLweSample, y::TransformedRLweSample) =
    TransformedRLweSample(x.params, x.a .+ y.a, x.current_variance + y.current_variance)


# TODO: (issue #7) how to compute the variance correctly?
Base.:*(x::TransformedRLweSample, y::Union{TransformedTorusPolynomial, TransformedTorusPolynomial64}) =
    TransformedRLweSample(x.params, x.a .* y, x.current_variance)

# TODO: (issue #7) how to compute the variance correctly?
Base.:*(x::RLweSample, y::TorusPolynomial) =
    RLweSample(x.params, x.a .* y, x.current_variance)
