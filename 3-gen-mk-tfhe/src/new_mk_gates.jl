function mk_gate_nand_new(ck::MKCloudKey_new, x::MKLweSample, y::MKLweSample; fast_boot::Bool = false)
    temp = (
        mk_lwe_noiseless_trivial(encode_message(1, 8), x.params, ck.parties)
        - x - y)
    ck.params.rlwe_is32 ? encode = encode_message : encode = encode_message64
    mk_bootstrap_new(ck.bootstrap_key, ck.keyswitch_key, encode(1, 8), temp, fast_boot)
end

function mk_gate_nand_new_wo_FFT(ck::MKCloudKey_new_wo_FFT, x::MKLweSample, y::MKLweSample; fast_boot::Bool = false)
    temp = (
        mk_lwe_noiseless_trivial(encode_message(1, 8), x.params, ck.parties)
        - x - y)
    ck.params.rlwe_is32 ? encode = encode_message : encode = encode_message64
    mk_bootstrap_new_wo_FFT(ck.bootstrap_key, ck.keyswitch_key, encode(1, 8), temp, fast_boot)
end
