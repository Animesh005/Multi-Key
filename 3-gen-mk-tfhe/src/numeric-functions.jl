using StatsBase

const Torus32 = Int32
const Torus64 = Int64


function rand_uniform_negative_binary(rng::AbstractRNG, dims...)
    rand(rng, [Int32(-1),Int32(0),Int32(1)], dims...)
end

function rand_negative_binary(rng::AbstractRNG, dims...)
    sample(rng,[Int32(-1),Int32(0),Int32(1)],Weights([0.113546097609674,1-2*0.113546097609674,0.113546097609674]),dims...)
end

 

function rand_uniform_bool(rng::AbstractRNG, dims...)
    rand(rng, Int32(0):Int32(1), dims...)
end


function rand_uniform_negative_binary64(rng::AbstractRNG, dims...)
    rand(rng, [Int64(-1),Int64(0),Int64(1)], dims...)
end

function rand_negative_binary64(rng::AbstractRNG, dims...)
    sample(rng,[Int64(-1),Int64(0),Int64(1)],Weights([0.113546097609674,1-2*0.113546097609674,0.113546097609674]),dims...)
end
 


function rand_uniform_bool64(rng::AbstractRNG, dims...)
    rand(rng, Int64(0):Int64(1), dims...)
end


function rand_uniform_torus32(rng::AbstractRNG, dims...)
    rand(rng, Torus32, dims...)
end


function rand_uniform_torus64(rng::AbstractRNG, dims...)
    rand(rng, Torus64, dims...)
end


function rand_gaussian_float(rng::AbstractRNG, sigma::Float64, dims...)
    randn(rng, dims...) .* sigma
end


# Gaussian sample centered in `message`, with standard deviation `sigma`
function rand_gaussian_torus32(rng::AbstractRNG, message::Torus32, sigma::Float64, dims...)
    err = randn(rng, dims...) .* sigma
    message .+ dtot32.(err)
end


function rand_gaussian_torus64(rng::AbstractRNG, message::Torus64, sigma::Float64, dims...)
    err = randn(rng, dims...) .* sigma
    message .+ dtot64.(err)
end


"""
Approximates the phase to the nearest message in range `[-message_space/2, message_space/2)`
in a space with `message_space` elements.
`message_space` must be a power of 2.
"""
function decode_message(phase::Torus32, message_space::Int)
    log2_ms = trailing_zeros(message_space)
    (phase + (one(Torus32) << (32 - log2_ms - 1))) >> (32 - log2_ms)
end

function decode_message64(phase::Torus64, message_space::Int64)
    log2_ms = trailing_zeros(message_space)
    (phase + (one(Torus64) << (64 - log2_ms - 1))) >> (64 - log2_ms)
end


"""
Returns the phase of the given message in range `[-message_space/2, message_space/2)`
in a space with `message_space` elements.
`message_space` must be a power of 2.
"""
function encode_message(mu::Int, message_space::Int)
    log2_ms = trailing_zeros(message_space)
    Torus32(mu) << (32 - log2_ms)
end


function encode_message64(mu::Int, message_space::Int)
    log2_ms = trailing_zeros(message_space)
    Torus64(mu) << (64 - log2_ms)
end


"""
Converts a double in range `[-0.5, 0.5)` to `Torus32`.
"""
function dtot32(d::Float64)
    trunc(Int32, d * 2^32)
end

function dtot64(d::Float64)
    trunc(Int64, d * 2^64)
end

function t64tot32(d::Torus64)
    trunc(Int32, d / 2^32)
end


"""
Calculates the noise of a phase.
"""
function noise_calc(m_torus::Torus32, d_torus::Torus32)

    m_torus=Float64(m_torus)/2^32
    d_torus=Float64(d_torus)/2^32

    if m_torus>0
        noise = (d_torus<0 && d_torus<(m_torus-0.5)) ?
        Float64(1.0) + d_torus - m_torus : d_torus - m_torus
    elseif m_torus < 0
        noise = (d_torus>m_torus+0.5) ?
        Float64(1.0) - d_torus + m_torus : d_torus - m_torus
    else
        noise = d_torus
    end
    return noise

end