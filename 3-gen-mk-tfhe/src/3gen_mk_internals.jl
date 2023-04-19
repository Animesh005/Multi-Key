"""
*This File contains structures and functions to perform Bootstrapping for the 3rd generation of MKTFHE.

*TODO : Verify if the MKBootstrapKey_3gen structure is necessary. (01/12/22)
"""


""" 3rd generation of Bootstrapping Keys structure. One BootstrapKeyPart_3gen contains the TRGSW encryptions of the 
coefficients of a party's LWE key using the common public keys of all parties."""
struct BootstrapKeyPart_3gen
    tgsw_params :: TGswParams
    rlwe_params :: RLweParams
    crp_a :: CRP_3gen
    gsw_key :: Array{TGswSample_3gen, 1}
    common_pubkey :: CommonPubKey_3gen
    key_size :: Int

    """ Bootstrapping key generation using the enhancements initially introduced and multiple CRPs for an unique randomness """
    function BootstrapKeyPart_3gen(
            rng:: AbstractRNG, lwe_key::LweKey, alpha_gsw::Float64, crp_a :: CRP_3gen, crp_a_prime :: Array{CRP_3gen,1},
            common_pubkey:: CommonPubKey_3gen, common_pubkey_prime:: Array{CommonPubKey_3gen,1}, tgsw_params::TGswParams, rlwe_params::RLweParams,wo_fft :: Int64 = 0)
        
        key_size= lwe_key.params.size
        if wo_fft==0
            gsw_key = [tgsw_encrypt_3gen(rng, lwe_key.key[i], alpha_gsw, common_pubkey, common_pubkey_prime[i], crp_a,crp_a_prime[i]) for i in 1:key_size] # gsw encryption obtained with new 3rd gen method of encryption
        else
            gsw_key = [tgsw_encrypt_3gen_wo_FFT(rng, lwe_key.key[i], alpha_gsw, common_pubkey, common_pubkey_prime[i], crp_a,crp_a_prime[i]) for i in 1:key_size] # gsw encryption obtained with new 3rd gen method of encryption
        end
        new(tgsw_params,rlwe_params,crp_a,gsw_key,common_pubkey,key_size)
    end

    """ Bootstrapping key generation using the simple version later introduced with one CRP but many randomness. """    
    function BootstrapKeyPart_3gen(
        rng:: AbstractRNG, lwe_key::LweKey, alpha_gsw::Float64, crp_a :: CRP_3gen,
        common_pubkey:: CommonPubKey_3gen, tgsw_params::TGswParams, rlwe_params::RLweParams,wo_FFT::Int64 = 0)
    
        key_size= lwe_key.params.size

        gsw_key = [tgsw_encrypt_3gen(rng, lwe_key.key[i], alpha_gsw, common_pubkey, crp_a,true,wo_FFT) for i in 1:key_size] # gsw encryption obtained with new 3rd gen method of encryption

        new(tgsw_params,rlwe_params,crp_a,gsw_key,common_pubkey,key_size)
    end
end

struct TransformedBootstrapKeyPart_3gen
    tgsw_params :: TGswParams
    rlwe_params :: RLweParams
    gsw_key :: Array{TransformedTGswSample_3gen, 1}
    key_size :: Int
    
    function TransformedBootstrapKeyPart_3gen(bk::BootstrapKeyPart_3gen)
        gsw_key = forward_transform.(bk.gsw_key)
        new(bk.tgsw_params,bk.rlwe_params,gsw_key,bk.key_size)
    end
end


""" Function to multiply homomorphically the accumulator with X^(barai*si) using the 3rd generation external multiplication. """
function mk_mux_rotate_3gen(accum::RLweSample, bki::TransformedTGswSample_3gen, barai::Int32)
    temp = mul_by_monomial(accum,barai)-accum
    accum + tgsw_extern_mul_3gen(temp,bki)
end


""" Function to run Blind Rotate for the i-th party using 3rd generation samples and external product."""
function mk_ith_blind_rotate_3gen(acc::RLweSample, gsw_key::Array{TransformedTGswSample_3gen, 1}, bara::Array{Int32, 1})
    for i in eachindex(bara)
        barai = bara[i]
        if barai != 0
            acc = mk_mux_rotate_3gen(acc, gsw_key[i], barai)
        end
    end
    acc
end


""" Function to run the complete MK BlindRotate with 3rd generation primitives."""
function mk_blind_rotate_3gen(accum::RLweSample, bk::Array{TransformedBootstrapKeyPart_3gen, 1}, bara::Array{Int32, 2})
    parties=length(bk)
     for i=1:parties
         accum=mk_ith_blind_rotate_3gen(accum, bk[i].gsw_key,bara[:,i])
     end
     accum
 end


""" Function to run the complete MK BlindRotate and Sample Extract with 3rd generation primitives."""
function mk_blind_rotate_and_extract_3gen(
    v::TorusPolynomial, bk::Array{TransformedBootstrapKeyPart_3gen, 1}, barb::Int32, bara::Array{Int32, 2})
parties = size(bara, 2)
testvectbis = mul_by_monomial(v, -barb)
acc = rlwe_noiseless_trivial(testvectbis, bk[1].rlwe_params)
acc = mk_blind_rotate_3gen(acc, bk, bara)
bk[1].rlwe_params.is32 ? rlwe_extract_sample(acc) : rlwe_extract_sample_64(acc)
end


""" Function to run the complete MK Bootstrap without Key switching with 3rd generation primitives."""
function mk_bootstrap_wo_keyswitch_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, mu::Union{Torus32, Torus64}, x::MKLweSample)

    p_degree = bk[1].rlwe_params.polynomial_degree
    barb = decode_message(x.b, p_degree * 2)
    bara = decode_message.(x.a, p_degree * 2)

    #the initial testvec = [mu,mu,mu,...,mu]
    testvect = torus_polynomial(repeat([mu], p_degree))
 
    mk_blind_rotate_and_extract_3gen(testvect, bk, barb, bara)
end

""" Function to perform the complete MK Bootstrap (including key switching) with 3rd generation primitives.""" 
function mk_bootstrap_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, mu::Union{Torus32, Torus64}, x::MKLweSample)
    u = mk_bootstrap_wo_keyswitch_3gen(bk, mu, x)
    # println("u:", typeof(u))
    mk_keyswitch_3gen(ks, u)
end

# function mk_bootstrap_3gen_gpu(bk::CuArray{TransformedBootstrapKeyPart_3gen, 1}, ks::CuArray{KeyswitchKey, 1}, mu::Union{Torus32, Torus64}, x::MKLweSample)
#     u = mk_bootstrap_wo_keyswitch_3gen(bk, mu, x)
#     # println("u:", typeof(u))
#     mk_keyswitch_3gen(ks, u)
# end