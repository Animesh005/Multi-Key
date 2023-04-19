using CUDA
using BenchmarkTools
using CUDAKernels, KernelAbstractions

# include("./src/TFHE.jl")
# using Random, Printf
# using .TFHE

function conv3d(input, input_height, input_width, kernels, kernel_size, number_kernels, 
                        output, output_height, output_width, stride)

    # @cuprintln "input_height = $input_height, input_width = $input_width, kernel_size = $kernel_size, output_height = $output_height, output_width = $output_width"
    
    tidx = threadIdx().x + (blockIdx().x - 1) * blockDim().x
    tidy = threadIdx().y + (blockIdx().y - 1) * blockDim().y
    tidz = threadIdx().z + (blockIdx().z - 1) * blockDim().z

    tmp = 0
    for m = 1:kernel_size
        for n = 1:kernel_size
            x = tidx * stride + m - 1
            y = tidy * stride + n - 1

            if (tidz >=0 && tidz <= number_kernels)
                if (x >= 0 && x <= input_height)
                    if (y >= 0 && y <= input_width)
                        # @cuprintln "kernel_idx = $((tidz-1)*kernel_size*kernel_size + (m-1)*kernel_size + n)"
                        # @cuprintln "tidx = $tidx, tidy = $tidy, tidz=$tidz, x = $x, y = $y, m = $m, n = $n"
                        tmp += input[(x-1)*input_width + y] * kernels[(tidz-1)*kernel_size*kernel_size + (m-1)*kernel_size + n]
                        # @cuprintln "tmp: $tmp"
                    end
                end
            end
        end 
    end

    if (tidz >=0 && tidz <= number_kernels)
        if (tidx >= 0 && tidx <= output_height)
            if (tidy >= 0 && tidy <= output_width)
                @cuprintln "tidx = $tidx, tidy = $tidy, tidz=$tidz, tmp: $tmp, index: $((tidz-1)*output_height*output_width + (tidx-1)*output_width + tidy)"
                output[(tidz-1)*output_height*output_width + (tidx-1)*output_width + tidy] = tmp
            end
        end
    end

    return

end

# function conv2d(input, input_height, input_width, kernels, kernel_size, 
#                     output, output_height, output_width, stride)

#     # @cuprintln "input_height = $input_height, input_width = $input_width, kernel_size = $kernel_size"

#     tidx = threadIdx().x + (blockIdx().x - 1) * blockDim().x
#     tidy = threadIdx().y + (blockIdx().y - 1) * blockDim().y

#     tmp = 0
#     for m = 1:kernel_size
#         for n = 1:kernel_size
#             x = tidx * stride + m - 1
#             y = tidy * stride + n - 1

#             if (x >= 0 && x <= input_height)
#                 if (y >= 0 && y <= input_width)
#                     # @cuprintln "tidx = $tidx, tidy = $tidy, x = $x, y = $y, m = $m, n = $n"
#                     tmp += input[(x-1)*input_width + y] * kernels[(m-1)*kernel_size + n]
#                     # @cuprintln "tmp: $tmp"
#                 end
#             end
            
#         end 
#     end

#     if (tidx >= 0 && tidx <= output_height)
#         if (tidy >= 0 && tidy <= output_width)
#             # @cuprintln "tidx = $tidx, tidy = $tidy"
#             output[(tidx-1)*output_width + tidy] = tmp
#         end
#     end

#     return
# end

function main()

    input_size = 9
    kernel_size = 3
    number_kernels = 4
    stride = 1
    padding = 0

    input = CuArray{Float32, 1}(undef, input_size * input_size)
    kernel = CuArray{Float32, 1}(undef, number_kernels * kernel_size * kernel_size)
    # kernel = CuArray{Float32, 1}(undef, kernel_size * kernel_size)

    input_height = Int64(CUDA.sqrt(size(input, 1)))
    input_width = input_height
    output_height = Int64((input_height - kernel_size) / stride) + 1
    output_width = Int64((input_width - kernel_size) / stride) + 1

    # println("output_height: ", output_height, " output_width: ", output_width)

    output = CuArray{Float32, 1}(undef, number_kernels * output_height * output_width)

    fill!(input, 5)
    fill!(kernel, 6)
    fill!(output, 0)

    # @benchmark conv2d($input, $kernels, $stride)
    # @cuda threads=(8, 8) blocks=4 conv2d(input, input_height, input_width, kernel, kernel_size,
    #                                         output, output_height, output_width, stride)

    @cuda threads=(1, 8, 16) blocks=8 conv3d(input, input_height, input_width, kernel, kernel_size,
                                            number_kernels, output, output_height, output_width, stride)

    # gpu_kernel = @cuda launch=false conv3d(input, input_height, input_width, kernel, kernel_size,
    #                                         number_kernels, output, output_height, output_width, stride)
    # config = CUDA.launch_configuration(gpu_kernel.fun)

    # println(config)

    for c = 1:number_kernels
        for i = 1:output_height
            for j = 1:output_width
                print(CUDA.@allowscalar output[(c-1)*output_height*output_width + (i-1)*output_width + j])
            end
            println()
        end
        println()
        println()
    end

end

main()
