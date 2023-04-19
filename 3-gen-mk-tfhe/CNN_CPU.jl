# include("./src/TFHE.jl")
# using Random, Printf
# using .TFHE

function conv3d(input, input_height, input_width, kernels, kernel_size, number_kernels, 
                        output, output_height, output_width, stride)
    
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
                        tmp += input[(x-1)*input_width + y] * kernels[(tidz-1)*kernel_size*kernel_size + (m-1)*kernel_size + n]
                    end
                end
            end
        end 
    end

    if (tidz >=0 && tidz <= number_kernels)
        if (tidx >= 0 && tidx <= output_height)
            if (tidy >= 0 && tidy <= output_width)
                output[(tidz-1)*output_height*output_width + (tidx-1)*output_width + tidy] = tmp
            end
        end
    end

    return

end

function main()

    input_size = 9
    kernel_size = 3
    number_kernels = 4
    stride = 1
    padding = 0

    input = Array{Float32, 1}(undef, input_size * input_size)
    kernel = Array{Float32, 1}(undef, number_kernels * kernel_size * kernel_size)
    # kernel = CuArray{Float32, 1}(undef, kernel_size * kernel_size)

    input_height = input_size
    input_width = input_size
    output_height = Int64((input_height - kernel_size) / stride) + 1
    output_width = Int64((input_width - kernel_size) / stride) + 1

    # println("output_height: ", output_height, " output_width: ", output_width)

    output = Array{Float32, 1}(undef, number_kernels * output_height * output_width)

    fill!(input, 5)
    fill!(kernel, 6)
    fill!(output, 0)

    conv3d(input, input_height, input_width, kernel, kernel_size,
                number_kernels, output, output_height, output_width, stride)

    for c = 1:number_kernels
        for i = 1:output_height
            for j = 1:output_width
                print(output[(c-1)*output_height*output_width + (i-1)*output_width + j])
            end
            println()
        end
        println()
        println()
    end

end

main()
