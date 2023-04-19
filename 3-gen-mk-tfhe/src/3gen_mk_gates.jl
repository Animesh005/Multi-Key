# using CUDA

"""
*This File contains the functions that run given gates homomorphically for the 3rd generation of MKTFHE.
"""

"""Function that computes the NAND gate between x and y using the 3rd generation of MKTFHE"""
function mk_gate_nand_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, x::MKLweSample, y::MKLweSample)
    temp = (
        mk_lwe_noiseless_trivial(encode_message(1, 8), x.params, length(bk))
        - x - y)
    bk[1].rlwe_params.is32 ? encode = encode_message : encode = encode_message64
    mk_bootstrap_3gen(bk, ks, encode(1, 8), temp)
end

function mk_gate_nand_3gen_wb(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, x::MKLweSample, y::MKLweSample)
    temp = (
        mk_lwe_noiseless_trivial(encode_message(1, 8), x.params, length(bk))
        - x - y)
    return temp
end

"""Function that computes the OR gate between x and y using the 3rd generation of MKTFHE"""
function mk_gate_or_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, x::MKLweSample, y::MKLweSample)
    temp = (
        mk_lwe_noiseless_trivial(encode_message(1, 8), x.params, length(bk))
        + x + y)
    bk[1].rlwe_params.is32 ? encode = encode_message : encode = encode_message64
    mk_bootstrap_3gen(bk,ks, encode(1, 8), temp)
end

function mk_gate_or_3gen_wb(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, x::MKLweSample, y::MKLweSample)
    temp = (
        mk_lwe_noiseless_trivial(encode_message(1, 8), x.params, length(bk))
        + x + y)
    return temp
end

"""Function that computes the AND gate between x and y using the 3rd generation of MKTFHE"""
function mk_gate_and_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, x::MKLweSample, y::MKLweSample)
    temp = (
        mk_lwe_noiseless_trivial(encode_message(-1, 8), x.params, length(bk))
        + x + y)
    bk[1].rlwe_params.is32 ? encode = encode_message : encode = encode_message64
    mk_bootstrap_3gen(bk,ks, encode(1, 8), temp)
end

function mk_gate_and_3gen_wb(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, x::MKLweSample, y::MKLweSample)
    temp = (
        mk_lwe_noiseless_trivial(encode_message(-1, 8), x.params, length(bk))
        + x + y)
    return temp
end

function mk_gate_3and_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, x::MKLweSample, y::MKLweSample, z::MKLweSample)
    temp = (
        mk_lwe_noiseless_trivial(encode_message(-1, 4), x.params, length(bk))
        + x + y + z)
    # temp = (
    #     mk_lwe_noiseless_trivial(encode_message(-1, 8), temp.params, length(bk))
    #     + temp + z)
    bk[1].rlwe_params.is32 ? encode = encode_message : encode = encode_message64
    mk_bootstrap_3gen(bk,ks, encode(1, 8), temp)
end


"""Function that computes the XOR gate between x and y using the 3rd generation of MKTFHE"""
function mk_gate_xor_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, x::MKLweSample, y::MKLweSample)
    temp = (
        mk_lwe_noiseless_trivial(encode_message(1, 4), x.params, length(bk))
        + convert(Torus32, 2)*x + convert(Torus32, 2)*y)
    bk[1].rlwe_params.is32 ? encode = encode_message : encode = encode_message64
    mk_bootstrap_3gen(bk,ks, encode(1, 8), temp)
end

function mk_gate_xor_3gen_wb(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, x::MKLweSample, y::MKLweSample)
    temp = (
        mk_lwe_noiseless_trivial(encode_message(1, 4), x.params, length(bk))
        + convert(Torus32, 2)*x + convert(Torus32, 2)*y)
    return temp
end

function mk_gate_not_3gen(x::MKLweSample)
    # Not bootstrapped, the bk and ks are just for the sake of interface uniformity.
    -x
end

"""
Applies the MUX (MUX(x, y, z) == x ? y : z == OR(AND(x, y), AND(NOT(x), z)))
gate to encrypted bits `x`, `y` and `z`.
"""
# function mk_gate_mux_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, x::MKLweSample, 
#                             y::MKLweSample, z::MKLweSample, secret_keys::Array{SecretKey_3gen, 1})

#     # compute `AND(x, y)`
#     t1 = (
#         mk_lwe_noiseless_trivial(encode_message(-1, 8), x.params, length(bk))
#         + x + y)
#     # u1 = mk_bootstrap_wo_keyswitch_3gen(bk, encode_message(1, 8), t1)
#     u1 = mk_bootstrap_3gen(bk, ks, encode_message(1, 8), t1)

#     println("u1: ", mk_decrypt_3gen(secret_keys, u1))

#     # compute `AND(NOT(x), z)`
#     t2 = (
#         mk_lwe_noiseless_trivial(encode_message(-1, 8), x.params, length(bk))
#         - x + z)
#     # u2 = mk_bootstrap_wo_keyswitch_3gen(bk, encode_message(1, 8), t2)
#     u2 = mk_bootstrap_3gen(bk, ks, encode_message(1, 8), t2)

#     println("u2: ", mk_decrypt_3gen(secret_keys, u2))

#     # compute `OR(u1,u2)`
#     # t3 = (
#     #     lwe_noiseless_trivial(encode_message(1, 8), u1.params)
#     #     + u1 + u2)

#     # t3 = u1 + u2

#     t3 = (
#         mk_lwe_noiseless_trivial(encode_message(1, 8), u1.params, length(bk))
#         + u1 + u2)

#     mk_bootstrap_3gen(bk, ks, encode_message(1, 8), t3)
#     # mk_keyswitch_3gen(ks, t3)

#     println("t3: ", mk_decrypt_3gen(secret_keys, t3))

#     return t3

# end

function mk_gate_mux_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, 
    x::MKLweSample, y::MKLweSample, z::MKLweSample)

    # compute `AND(x, y)`
    t1 = mk_gate_and_3gen(bk, ks, x, y)

    # compute `AND(NOT(x), z)`
    t2 = mk_gate_and_3gen(bk, ks, -x, z)

    # compute `AND(x, y) + AND(NOT(x), z)`
    # t3 = mk_gate_or_3gen(bk, ks, t1, t2)

    t3 = (mk_lwe_noiseless_trivial(encode_message(1, 8), t1.params, length(bk))
            + t1 + t2)

    return t3

end

function mk_copy_3gen(x::MKLweSample)
    temp = MKLweSample(x.params, x.a, x.b, x.current_variance)

    return temp
end

# function mk_int_add_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, a::Vector{MKLweSample}, b::Vector{MKLweSample}, Cin::MKLweSample, WIDTH)

#     result = Array{MKLweSample}(undef, WIDTH)
#     _cin = Cin
#     for i=1:WIDTH
#         tmp1 = mk_gate_xor_3gen(bk, ks, a[i], b[i])
#         tmp2 = mk_gate_and_3gen(bk, ks, a[i], b[i])

#         if (!isnothing(_cin))
    #         result[i] = mk_gate_xor_3gen(bk, ks, tmp1, _cin)
    #         tmp3 = mk_gate_and_3gen(bk, ks, tmp1, _cin)
    #         carry = mk_gate_or_3gen(bk, ks, tmp2, tmp3)
#         else
#           result[i] = mk_copy_3gen(tmp1)
#           carry = mk_copy_3gen(tmp2)
#         end

#         _cin = carry
#     end

#     return result

# end

# Integer addition circuit
function mk_add_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, a::Vector{MKLweSample}, b::Vector{MKLweSample}, Cin::MKLweSample, WIDTH)

    result = Array{MKLweSample}(undef, WIDTH)
    _cin = Cin
    for i=1:WIDTH
        tmp1 = mk_gate_xor_3gen(bk, ks, a[i], b[i])
        tmp2 = mk_gate_and_3gen(bk, ks, a[i], b[i])

        result[i] = mk_gate_xor_3gen(bk, ks, tmp1, _cin)
        tmp3 = mk_gate_and_3gen(bk, ks, tmp1, _cin)
        carry = mk_gate_or_3gen(bk, ks, tmp2, tmp3)

        _cin = carry
    end

    return result

end

# Integer addition circuit
function mk_add_3gen_v2(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, a::Vector{MKLweSample}, b::Vector{MKLweSample}, Cin::MKLweSample, WIDTH)

    result = Array{MKLweSample}(undef, WIDTH)
    _cin = Cin
    for i=1:WIDTH
        tmp1 = mk_gate_xor_3gen(bk, ks, a[i], b[i])
        tmp2 = mk_gate_and_3gen(bk, ks, a[i], b[i])

        result[i] = mk_gate_xor_3gen(bk, ks, tmp1, _cin)
        tmp3 = mk_gate_and_3gen(bk, ks, tmp1, _cin)
        carry = mk_gate_or_3gen(bk, ks, tmp2, tmp3)

        _cin = carry
    end

    return result

end

# Inversion circuit
function mk_inv_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, a::Vector{MKLweSample}, one::MKLweSample, WIDTH)

    result = Array{MKLweSample}(undef, WIDTH)

    for i=1:WIDTH
        result[i] = mk_gate_xor_3gen(bk, ks, a[i], one)
    end

    return result

end

# Integer substraction circuit
function mk_sub_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, a::Vector{MKLweSample}, b::Vector{MKLweSample}, one::MKLweSample, WIDTH)

    tmp = mk_inv_3gen(bk, ks, b, one, WIDTH)

    result = mk_add_3gen(bk, ks, a, tmp, one, WIDTH)

    return result

end

# Less-than circuit
function mk_less_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, a::Vector{MKLweSample}, b::Vector{MKLweSample}, one::MKLweSample, WIDTH)

    tmp = mk_sub_3gen(bk, ks, a, b, one, WIDTH)

    result = mk_copy_3gen(tmp[WIDTH])

    return result

end

# Less-than circuit
function mk_grt_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, a::Vector{MKLweSample}, b::Vector{MKLweSample}, one::MKLweSample, WIDTH)

    tmp = mk_sub_3gen(bk, ks, b, a, one, WIDTH)

    result = mk_copy_3gen(tmp[WIDTH])

    return result

end

# Less-than equal circuit
function mk_leq_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, a::Vector{MKLweSample}, b::Vector{MKLweSample}, one::MKLweSample, WIDTH)

    tmp = mk_grt_3gen(bk, ks, a, b, one, WIDTH)

    result = mk_gate_xor_3gen(bk, ks, tmp, one)

    return result

end

# Less-than equal circuit
function mk_geq_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, a::Vector{MKLweSample}, b::Vector{MKLweSample}, one::MKLweSample, WIDTH)

    tmp = mk_less_3gen(bk, ks, a, b, one, WIDTH)

    result = mk_gate_xor_3gen(bk, ks, tmp, one)

    return result

end


function mk_int_add_with_carry_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, a::Vector{MKLweSample}, b::Vector{MKLweSample}, Cin::MKLweSample, WIDTH)

    result = Array{MKLweSample}(undef, WIDTH+1)
    _cin = Cin
    for i=1:WIDTH
        tmp1 = mk_gate_xor_3gen(bk, ks, a[i], b[i])
        tmp2 = mk_gate_and_3gen(bk, ks, a[i], b[i])

        result[i] = mk_gate_xor_3gen(bk, ks, tmp1, _cin)
        tmp3 = mk_gate_and_3gen(bk, ks, tmp1, _cin)
        carry = mk_gate_or_3gen(bk, ks, tmp2, tmp3)

        _cin = carry
    end

    result[WIDTH+1] = _cin

    return result

end

function mk_int_mul_3gen(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, a::Vector{MKLweSample}, b::Vector{MKLweSample}, ZERO::MKLweSample, WIDTH)
    
    BArr = Array{MKLweSample, 2}(undef, WIDTH, WIDTH)
    res = Array{MKLweSample}(undef, WIDTH)
    result = Array{MKLweSample}(undef, 2*WIDTH)

    for i=1:WIDTH
        for j=1:WIDTH
            BArr[i, j] = mk_gate_and_3gen(bk, ks, a[j], b[i])
        end
    end

    result[1] = mk_copy_3gen(BArr[1, 1])

    tmpIn = Array{MKLweSample}(undef, WIDTH)

    for i=1:WIDTH-1
        tmpIn[i] = mk_copy_3gen(BArr[1, i+1])
    end

    tmpIn[WIDTH] = mk_copy_3gen(ZERO)
    
    ctr = 1

    for i=2:WIDTH-1
        tmpArr = Array{MKLweSample}(undef, WIDTH+1)
        tmpArr = mk_int_add_with_carry_3gen(bk, ks, tmpIn, BArr[i, :], ZERO, WIDTH)

        result[i] = mk_copy_3gen(tmpArr[1])

        for j=1:WIDTH
            tmpIn[j] = mk_copy_3gen(tmpArr[j+1])
        end

        ctr = i

    end

    tmpArr = mk_int_add_with_carry_3gen(bk, ks, tmpIn, BArr[ctr, :], ZERO, WIDTH)

    for i=1:WIDTH+1
        result[i+ctr] = mk_copy_3gen(tmpArr[i])
    end

    for i=1:WIDTH
        res[i] = mk_copy_3gen(result[i])
    end

    return res

end

function enc_conv2d(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1}, input::Array{MKLweSample, 2}, 
                    ZERO::MKLweSample, kernels::Array{MKLweSample, 3}, stride::Int, padding::Int, WIDTH)

    input_height = size(input, 1)
    input_width = size(input, 2)

    number_kernels = size(kernels, 1)
    kernel_size = size(kernels, 2)
    
    output_height = (input_height - kernel_size) / stride + 1
    output_width = (input_width - kernel_size) / stride + 1

    outputs = Array{MKLweSample, 3}(undef, number_kernels, output_height, output_width)

    for c = 1:number_kernels
        for i = 1:output_height
            for j = 1:output_width
                sum = Array{MKLweSample}(undef, WIDTH)
                
                for m = 0:kernel_size
                    for n = 0:kernel_size
                        x = i * stride + m
                        y = j * stride + n

                        mulTmp = mk_int_mul_3gen(bk, ks, input[x, y], kernels[c, m, n], ZERO, WIDTH)
                        sum = mk_int_add_3gen(bk, ks, sum, mulTmp, ZERO, WIDTH)
                    end 
                end
            end
        end
    end

    return outputs
end

# function conv2d_clear(input::CuArray{Float32, 2}, kernels::CuArray{Float32, 3}, stride)

#     input_height = size(input, 1)
#     input_width = size(input, 2)

#     number_kernels = size(kernels, 1)
#     kernel_size = size(kernels, 2)

#     output_height = (input_height - kernel_size) / stride + 1
#     output_width = (input_width - kernel_size) / stride + 1

#     outputs = CuArray{Float32, 3}(undef, number_kernels, output_height, output_width)

#     for c = 1:number_kernels
#         for i = 1:output_height
#             for j = 1:output_width
#                 sum = CuArray{Float32}(undef, 1)
#                 for m = 0:kernel_size
#                     for n = 0:kernel_size
#                         x = i * stride + m
#                         y = j * stride + n

#                         sum[1] += input[x, y] * kernels[c, m, n]
                        
#                     end 
#                 end

#                 outputs[c, i, j] = sum[1]
#             end
#         end
#     end

#     return outputs
# end


############## GPU Version ###################

function mk_gate_xor_3gen_gpu(bk, ks, x, y)
    temp = (
        mk_lwe_noiseless_trivial(encode_message(1, 4), x.params, length(bk))
        + convert(Torus32, 2)*x + convert(Torus32, 2)*y)
    # bk[1].rlwe_params.is32 ? encode = encode_message : encode = encode_message64
    # mk_bootstrap_3gen(bk,ks, encode(1, 8), temp)

    return 
end

function mk_int_add_3gen_gpu(bk, ks, a, b, Cin::MKLweSample, WIDTH)

    result = CuArray{MKLweSample, 1}(undef, WIDTH)
    _cin = Cin
    for i=1:WIDTH
        tmp1 = mk_gate_xor_3gen(bk, ks, a[i], b[i])
        tmp2 = mk_gate_and_3gen(bk, ks, a[i], b[i])

        result[i] = mk_gate_xor_3gen(bk, ks, tmp1, _cin)
        tmp3 = mk_gate_and_3gen(bk, ks, tmp1, _cin)
        carry = mk_gate_or_3gen(bk, ks, tmp2, tmp3)

        _cin = carry
    end

    return result

end