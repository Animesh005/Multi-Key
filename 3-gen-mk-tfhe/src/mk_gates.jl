"""
    mk_gate_nand(ck::MKCloudKey, x::MKLweSample, y::MKLweSample)

Applies the NAND gate to encrypted bits `x` and `y`.
Returns a [`MKLweSample`](@ref) object.
"""
function mk_gate_nand(ck::MKCloudKey, x::MKLweSample, y::MKLweSample)
    temp = (
        mk_lwe_noiseless_trivial(encode_message(1, 8), x.params, ck.parties)
        - x - y)
    ck.params.rlwe_is32 ? encode = encode_message : encode = encode_message64
    mk_bootstrap(ck.bootstrap_key, ck.keyswitch_key, encode(1, 8), temp)
end

"""
    mk_gate_mux(ck::CloudKey, x::LweSample, y::LweSample, z::LweSample)

Applies the MUX (MUX(x, y, z) == x ? y : z == OR(AND(x, y), AND(NOT(x), z)))
gate to encrypted bits `x`, `y` and `z`.
Returns a [`LweSample`](@ref) object.
"""
# function mk_gate_mux(ck::MKCloudKey, x::MKLweSample, y::MKLweSample, z::MKLweSample)

#     # compute `AND(x, y)`
#     t1 = mk_lwe_noiseless_trivial(encode_message(-1, 8), x.params, ck.parties) + x + y
#     u1 = mk_bootstrap_wo_keyswitch_3gen(ck.bootstrap_key, encode_message(1, 8), t1)

#     # compute `AND(NOT(x), z)`
#     t2 = mk_lwe_noiseless_trivial(encode_message(-1, 8), x.params, ck.parties) - x + z
#     u2 = mk_bootstrap_wo_keyswitch_3gen(ck.bootstrap_key, encode_message(1, 8), t2)

#     # compute `OR(u1,u2)`
#     t3 = mk_lwe_noiseless_trivial(encode_message(1, 8), u1.params, ck.parties) + u1 + u2

#     mk_keyswitch_3gen(ck.keyswitch_key, t3)
# end
