# using CUDA

# # struct ArrayStruct{A}
# #     xs::Int
# #     ys::A
# # end

# # function (ast::ArrayStruct)(x)
# #     div = ast.ys / ast.xs
# #     sum = div + x
# # end

# # # xs_cpu = Array{Int32}(undef, 10)
# # # fill!(xs_cpu, 10)

# # xs_cpu = 5

# # ys_cpu = Array{Int32}(undef, 10)
# # fill!(ys_cpu, 20)

# # ast_cpu = ArrayStruct(xs_cpu, ys_cpu)

# # div_cpu = Array{Int32}(undef, 10)
# # fill!(div_cpu, 10)

# # result_cpu = ast_cpu.(div_cpu)

# # println(result_cpu)

# # # xs = CuArray(xs_cpu)
# # ys = CuArray(ys_cpu)

# # ast = ArrayStruct(xs_cpu, ys)

# # result = ast.(div_cpu)

# # println(result)

# struct ArrayStruct{A}
#     xs::Float64
#     ys::A
#     size::Int64

#     ArrayStruct(xs::Float64, ys, size::Int64) = new{typeof(ys)}(xs, ys, size)

#     function ArrayStruct(xs::Float64, size::Int64)
#         new{Array{Int32}}(xs, Array{Int32}(undef, size), size)
#     end

#     # function ArrayStruct(xs::Float64, ys, size::Int64)
#     #     new{typeof(ys)}(xs, ys, size)
#     # end
# end

# xs = 5.5
# size = 10
# ys = Array{Int32}(undef, size)
# fill!(ys, 20)

# ys = CuArray(ys)
# # println(typeof(ys))

# ast = ArrayStruct(xs, ys, size)

# println(typeof(ast.ys))
# println(ast.ys)

# using CUDA

# # Define your structure containing an array
# mutable struct MyStruct
#     x::Array{Float32}
# end

# # Create an instance of your structure
# s = MyStruct(rand(Float32, 10))

# # Convert the array in the structure to a CuArray
# s.x = cu(s.x)

# # Define your kernel function
# function my_kernel(s::MyStruct)
#     i = threadIdx().x
#     s.x[i] = s.x[i] * 2
#     return nothing
# end

# # Launch the kernel on the GPU
# @cuda threads=10 my_kernel(s)

# # Convert the CuArray back to a regular Array
# s.x = Array(s.x)

# println(s.x)

import Adapt
using CUDA

# Wraps the vector on the CPU side
# struct Data{T}
#     values::CuVector{T}
# end
struct Data{T<:AbstractArray}
    values::T
end

# Wraps the vector on the GPU side
# struct DataOnGPU{T}
#     values::CuDeviceVector{T}
# end

# Convert CPU struct to GPU struct
# function Adapt.adapt_structure(to, val::Data)
#     v = Adapt.adapt_structure(to, val.values)
#     DataOnGPU(v)
# end

# function Adapt.adapt_structure(to, val::Data)
#     v = Adapt.adapt_structure(to, val.values)
#     Data(v)
# end

# # GPU code
# function kernel(data::Data)
#     # Do nothing for now
#     return
# end

# # Create some random values and wrap them in the custom struct
# values = rand(Int32, 10) |> CuVector
# data = Data(values)

# # Run the kernel
# kernel = @cuda launch=false kernel(data)
# config = launch_configuration(kernel.fun)
# kernel(data; threads=config.threads, blocks=config.blocks)
# synchronize()

using CUDA

struct Interpolate{A}
    xs::A
    ys::A
end

Adapt.@adapt_structure Interpolate

function (itp::Interpolate)(x)
    i = searchsortedfirst(itp.xs, x)
    i = clamp(i, firstindex(itp.ys), lastindex(itp.ys))
    @inbounds itp.ys[i]
end

xs_cpu = [1.0, 2.0, 3.0]
ys_cpu = [10.0,20.0,30.0]
itp_cpu = Interpolate(xs_cpu, ys_cpu)
pts_cpu = [1.1,2.3]
result_cpu = itp_cpu.(pts_cpu)

println(result_cpu)

itp = Interpolate(CuArray(xs_cpu), CuArray(ys_cpu))
pts = CuArray(pts_cpu)

println(isbitstype(typeof(itp.xs)))
println(typeof(itp.ys))

println(isbitstype(typeof(itp)))

# import Adapt
# function Adapt.adapt_structure(to, itp::Interpolate)
#     xs = Adapt.adapt_structure(to, itp.xs)
#     ys = Adapt.adapt_structure(to, itp.ys)
#     Interpolate(xs, ys)
# end

result = itp.(pts)

print(result)
