# using Base.Threads

# function parallel_sum(A)
#     @assert nthreads() > 1 "Requires multiple threads"
    
#     s = 0
#     @threads for i in eachindex(A)
#         s += A[i]
#     end
#     return s
# end

# A = rand(10_000_000)
# println("Non parallel")
# @time sum(A) # Non-parallel sum

# println("Parallel")
# @time parallel_sum(A) # Parallel sum

# using Distributed

# # add worker processes
# proc_ids = addprocs(2)
# println(proc_ids)

# function my_function()
#     # task 1
#     @spawnat proc_ids[1] begin
#         # code for task 1 on process 1
#         println("Hello process 1")
#     end
    
#     # task 2
#     @spawnat proc_ids[2] begin
#         # code for task 2 on process 2
#         println("Hello process 2")
#     end

#     println("End of function")

#     return
    
# end

# # call function on process 1
# my_function()

using Distributed

# add worker processes
proc_ids = addprocs(2)
println(proc_ids)

function my_function()
    # task 1
    t1 = @spawnat proc_ids[1] begin
        # code for task 1 on process 1
        println("Hello process 1")
    end
    
    # task 2
    t2 = @spawnat proc_ids[2] begin
        # code for task 2 on process 2
        println("Hello process 2")
    end
    
    # Wait for both tasks to complete
    @sync for t in (t1, t2)
        wait(t)
    end

    println("End of function")

    return
end

# call function on process 1
my_function()


# function VolumeMatch(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1},
#     ord::EncOrders, resOrd::EncOrders,
#     accBuy::Vector{MKLweSample}, accSell::Vector{MKLweSample},
#     one::MKLweSample, zero::MKLweSample, WIDTH, secret_keys::Array{SecretKey_3gen, 1})

#     println("accBuy: ", mk_int_decrypt_3gen(secret_keys, accBuy, WIDTH))
#     println("accSell: ", mk_int_decrypt_3gen(secret_keys, accSell, WIDTH))

#     t1 = @spawnat proc_ids[1] begin
#     println("accBuy 1: ", mk_int_decrypt_3gen(secret_keys, accBuy, WIDTH))
#     for x in ord.buy
#     accTmp1 = mk_add_3gen(bk, ks, accBuy, x, zero, WIDTH)

#     for i = 1:WIDTH
#     accBuy[i] = mk_copy_3gen(accTmp1[i])
#     end
#     end

#     println("accBuy 2: ", mk_int_decrypt_3gen(secret_keys, accBuy, WIDTH))
#     return accBuy
#     end

#     t2 = @spawnat proc_ids[2] begin
#     println("accSell 1: ", mk_int_decrypt_3gen(secret_keys, accSell, WIDTH))
#     for x in ord.sell
#     accTmp2 = mk_add_3gen(bk, ks, accSell, x, zero, WIDTH)

#     for i = 1:WIDTH
#     accSell[i] = mk_copy_3gen(accTmp2[i])
#     end
#     end

#     println("accSell 2: ", mk_int_decrypt_3gen(secret_keys, accSell, WIDTH))
#     return accSell
#     end

#     # Wait for both tasks to complete
#     @sync for t in (t1, t2)
#     wait(t)
#     end

#     # accBuy = remotecall_fetch(fetch, proc_ids[1], t1)
#     # accSell = remotecall_fetch(fetch, proc_ids[2], t2)

#     accBuy = fetch(accBuy)
#     accSell = fetch(accSell)

#     println("accBuy: ", mk_int_decrypt_3gen(secret_keys, accBuy, WIDTH))
#     println("accSell: ", mk_int_decrypt_3gen(secret_keys, accSell, WIDTH))

#     # for x in ord.buy
#     #     accTmp1 = mk_add_3gen(bk, ks, accBuy, x, zero, WIDTH)

#     #     for i = 1:WIDTH
#     #         accBuy[i] = mk_copy_3gen(accTmp1[i])
#     #     end
#     # end

#     # for x in ord.sell
#     #     accTmp2 = mk_add_3gen(bk, ks, accSell, x, zero, WIDTH)

#     #     for i = 1:WIDTH
#     #         accSell[i] = mk_copy_3gen(accTmp2[i])
#     #     end
#     # end

#     sellGRTbuy = mk_grt_3gen(bk, ks, accSell, accBuy, one, WIDTH)

#     total1 = Array{MKLweSample}(undef, WIDTH)
#     total2 = Array{MKLweSample}(undef, WIDTH)
#     totalTmp = Array{MKLweSample}(undef, WIDTH)

#     # Threads.@threads for i = 1:WIDTH
#     #     id = Threads.threadid()
#     #     println("id: ", id)
#     #     total1[id] = mk_gate_mux_3gen(bk, ks, sellGRTbuy, accBuy[id], accSell[id])
#     #     total2[id] = mk_gate_mux_3gen(bk, ks, sellGRTbuy, accBuy[id], accSell[id])
#     # end

#     for i = 1:WIDTH
#     muxTmp = mk_gate_mux_3gen(bk, ks, sellGRTbuy, accBuy[i], accSell[i])
#     # total1[i] = mk_gate_mux_3gen(bk, ks, sellGRTbuy, accBuy[i], accSell[i])
#     # total2[i] = mk_gate_mux_3gen(bk, ks, sellGRTbuy, accBuy[i], accSell[i])
#     total1[i] = muxTmp
#     total2[i] = muxTmp
#     end

#     m = size(ord.buy, 1)

#     for i = 1:m
#     ordLeq = mk_leq_3gen(bk, ks, ord.buy[i], total1, one, WIDTH)
#     res = Array{MKLweSample}(undef, WIDTH)

#     # Threads.@threads for j = 1:WIDTH
#     #     id = Threads.threadid()
#     #     res[id] = mk_gate_mux_3gen(bk, ks, ordLeq, ord.buy[i][id], total1[id])
#     # end

#     for j = 1:WIDTH
#     res[j] = mk_gate_mux_3gen(bk, ks, ordLeq, ord.buy[i][j], total1[j])
#     end

#     totalTmp = mk_sub_3gen(bk, ks, total1, res, one, WIDTH)

#     # Threads.@threads for j = 1:WIDTH
#     #     id = Threads.threadid()
#     #     total1[id] = mk_copy_3gen(totalTmp[id])
#     # end

#     for j = 1:WIDTH
#     total1[j] = mk_copy_3gen(totalTmp[j])
#     end

#     push!(resOrd.buy, res)
#     end

#     n = size(ord.sell, 1)

#     for i = 1:n
#     ordLeq = mk_leq_3gen(bk, ks, ord.sell[i], total2, one, WIDTH)
#     res = Array{MKLweSample}(undef, WIDTH)

#     for j = 1:WIDTH
#     res[j] = mk_gate_mux_3gen(bk, ks, ordLeq, ord.sell[i][j], total2[j])
#     end

#     totalTmp = mk_sub_3gen(bk, ks, total2, res, one, WIDTH)

#     for j = 1:WIDTH
#     total2[j] = mk_copy_3gen(totalTmp[j])
#     end

#     push!(resOrd.sell, res)
#     end

# end




#############################################









# function VolumeMatch(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1},
#     ord::EncOrders, resOrd::EncOrders,
#     accBuy::Vector{MKLweSample}, accSell::Vector{MKLweSample},
#     one::MKLweSample, zero::MKLweSample, WIDTH, secret_keys::Array{SecretKey_3gen, 1})

# println("accBuy: ", mk_int_decrypt_3gen(secret_keys, accBuy, WIDTH))
# println("accSell: ", mk_int_decrypt_3gen(secret_keys, accSell, WIDTH))

# t1 = @spawnat proc_ids[1] begin
# println("accBuy 1: ", mk_int_decrypt_3gen(secret_keys, accBuy, WIDTH))
# for x in ord.buy
# accTmp1 = mk_add_3gen(bk, ks, accBuy, x, zero, WIDTH)

# for i = 1:WIDTH
# accBuy[i] = mk_copy_3gen(accTmp1[i])
# end
# end

# println("accBuy 2: ", mk_int_decrypt_3gen(secret_keys, accBuy, WIDTH))
# return accBuy
# end

# t2 = @spawnat proc_ids[2] begin
# println("accSell 1: ", mk_int_decrypt_3gen(secret_keys, accSell, WIDTH))
# for x in ord.sell
# accTmp2 = mk_add_3gen(bk, ks, accSell, x, zero, WIDTH)

# for i = 1:WIDTH
# accSell[i] = mk_copy_3gen(accTmp2[i])
# end
# end

# println("accSell 2: ", mk_int_decrypt_3gen(secret_keys, accSell, WIDTH))
# return accSell
# end

# # Wait for both tasks to complete
# @sync for t in (t1, t2)
# wait(t)
# end

# # accBuy = remotecall_fetch(fetch, proc_ids[1], t1)
# # accSell = remotecall_fetch(fetch, proc_ids[2], t2)

# accBuy = fetch(t1)
# accSell = fetch(t2)

# println("accBuy: ", mk_int_decrypt_3gen(secret_keys, accBuy, WIDTH))
# println("accSell: ", mk_int_decrypt_3gen(secret_keys, accSell, WIDTH))


# sellGRTbuy = mk_grt_3gen(bk, ks, accSell, accBuy, one, WIDTH)

# total1 = Array{MKLweSample}(undef, WIDTH)
# total2 = Array{MKLweSample}(undef, WIDTH)
# totalTmp = Array{MKLweSample}(undef, WIDTH)

# # # dtotal1 = distribute(total1)
# # # dtotal2 = distribute(total2)

# # dt = @distributed for i = 1:WIDTH
# #     # id = myid()
# #     total1[i] = mk_gate_mux_3gen(bk, ks, sellGRTbuy, accBuy[i], accSell[i])
# #     # println("id before: ", id, " muxTmp: ", mk_decrypt_3gen(secret_keys, muxTmp))
# #     # dtotal1[i] = muxTmp
# #     # dtotal2[i] = muxTmp
# #     # setindex!(dtotal1, i, muxTmp)
# #     # setindex!(dtotal1, i, muxTmp)
# #     # println("id after: ", id, " muxTmp: ", mk_decrypt_3gen(secret_keys, muxTmp))
# # end

# # # wait for distributed loop to finish
# # wait(dt)

# # total1 = fetch(dt)
# # total2 = fetch(dt)

# # for i = 1:WIDTH
# #     println("total1: ", mk_decrypt_3gen(secret_keys, total1[i]))
# # end
# # for i = 1:WIDTH
# #     println("total2: ", mk_decrypt_3gen(secret_keys, total2[i]))
# # end

# println("num threads: ", Threads.nthreads())

# # Threads.@threads for i = 1:WIDTH
# #     id = Threads.threadid()
# #     # if mod(i, Threads.nthreads()) == id
# #         println("Thread id: ", id)
# #         muxTmp = mk_gate_mux_3gen(bk, ks, sellGRTbuy, accBuy[id], accSell[id])
# #         println("muxTmp: ", mk_decrypt_3gen(secret_keys, muxTmp))
# #         total1[id] = muxTmp
# #         total2[id] = muxTmp
# #     # end
# # end

# # for i = 1:WIDTH
# #     total1[i] = mk_gate_mux_3gen(bk, ks, sellGRTbuy, accBuy[i], accSell[i])
# #     total2[i] = total1[i]
# # end

# # for i = 1:WIDTH
# #     println("total1: ", mk_decrypt_3gen(secret_keys, total1[i]))
# # end

# # for i = 1:WIDTH
# #     println("total2: ", mk_decrypt_3gen(secret_keys, total2[i]))
# # end

# total_t1 = Array{MKLweSample}(undef, WIDTH)
# total_t2 = Array{MKLweSample}(undef, WIDTH)

# Threads.@threads for i = 1:WIDTH
# id = Threads.threadid()
# @atomic total_t1[id] = mk_gate_mux_3gen(bk, ks, sellGRTbuy, accBuy[id], accSell[id])
# # println("total_t1: ", mk_decrypt_3gen(secret_keys, total_t1[id]))
# # println("id: ", id)
# end

# println()

# for i = 1:WIDTH
# println("total_t1: ", mk_decrypt_3gen(secret_keys, total_t1[i]))
# end

# total_t2 = total_t1

# for i = 1:WIDTH
# println("total_t2: ", mk_decrypt_3gen(secret_keys, total_t2[i]))
# end

# Threads.@threads for i = 1:WIDTH
# id = Threads.threadid()
# println("id: ", id)
# total1[id] = mk_gate_mux_3gen(bk, ks, sellGRTbuy, accBuy[id], accSell[id])
# total2[id] = mk_gate_mux_3gen(bk, ks, sellGRTbuy, accBuy[id], accSell[id])
# end

# for i = 1:WIDTH
# println("total1: ", mk_decrypt_3gen(secret_keys, total1[i]))
# end
# for i = 1:WIDTH
# println("total2: ", mk_decrypt_3gen(secret_keys, total2[i]))
# end

# t3 = @spawnat proc_ids[3] begin
# m = size(ord.buy, 1)
# println("m: ", m)
# buy = []

# for i = 1:m
# ordLeq = mk_leq_3gen(bk, ks, ord.buy[i], total1, one, WIDTH)
# res = Array{MKLweSample}(undef, WIDTH)

# for j = 1:WIDTH
# res[j] = mk_gate_mux_3gen(bk, ks, ordLeq, ord.buy[i][j], total1[j])
# end

# totalTmp = mk_sub_3gen(bk, ks, total1, res, one, WIDTH)

# for j = 1:WIDTH
# total1[j] = mk_copy_3gen(totalTmp[j])
# end

# # push!(resOrd.buy, res)
# push!(buy, res)
# end

# println("buy : ", mk_int_decrypt_3gen(secret_keys, buy[1], WIDTH))
# return buy
# end

# t4 = @spawnat proc_ids[4] begin
# n = size(ord.sell, 1)
# println("n: ", n)
# sell = []

# for i = 1:n
# ordLeq = mk_leq_3gen(bk, ks, ord.sell[i], total2, one, WIDTH)
# res = Array{MKLweSample}(undef, WIDTH)

# for j = 1:WIDTH
# res[j] = mk_gate_mux_3gen(bk, ks, ordLeq, ord.sell[i][j], total2[j])
# end

# totalTmp = mk_sub_3gen(bk, ks, total2, res, one, WIDTH)

# for j = 1:WIDTH
# total2[j] = mk_copy_3gen(totalTmp[j])
# end

# push!(sell, res)
# end

# println("sell : ", mk_int_decrypt_3gen(secret_keys, sell[1], WIDTH))
# return sell
# end

# # Wait for both tasks to complete
# @sync for t in (t3, t4)
# wait(t)
# end

# buy = fetch(t3)
# sell = fetch(t4)

# println("buy : ", mk_int_decrypt_3gen(secret_keys, buy[1], WIDTH))
# println("sell : ", mk_int_decrypt_3gen(secret_keys, sell[1], WIDTH))

# resOrd.buy = buy
# resOrd.sell = sell

# end


########################################

# updated Volume Match Algorithm

# function VolumeMatch(bk::Array{TransformedBootstrapKeyPart_3gen, 1}, ks::Array{KeyswitchKey, 1},
#     ord::EncOrders, resOrd::EncOrders,
#     accBuy::Vector{MKLweSample}, accSell::Vector{MKLweSample},
#     one::MKLweSample, zero::MKLweSample, WIDTH, secret_keys::Array{SecretKey_3gen, 1})

# println("accBuy: ", mk_int_decrypt_3gen(secret_keys, accBuy, WIDTH))
# println("accSell: ", mk_int_decrypt_3gen(secret_keys, accSell, WIDTH))

# t1 = @spawnat proc_ids[1] begin
# println("accBuy 1: ", mk_int_decrypt_3gen(secret_keys, accBuy, WIDTH))
# for x in ord.buy
# accTmp1 = mk_add_3gen(bk, ks, accBuy, x, zero, WIDTH)

# for i = 1:WIDTH
# accBuy[i] = mk_copy_3gen(accTmp1[i])
# end
# end

# println("accBuy 2: ", mk_int_decrypt_3gen(secret_keys, accBuy, WIDTH))
# return accBuy
# end

# t2 = @spawnat proc_ids[2] begin
# println("accSell 1: ", mk_int_decrypt_3gen(secret_keys, accSell, WIDTH))
# for x in ord.sell
# accTmp2 = mk_add_3gen(bk, ks, accSell, x, zero, WIDTH)

# for i = 1:WIDTH
# accSell[i] = mk_copy_3gen(accTmp2[i])
# end
# end

# println("accSell 2: ", mk_int_decrypt_3gen(secret_keys, accSell, WIDTH))
# return accSell
# end

# # Wait for both tasks to complete
# @sync for t in (t1, t2)
# wait(t)
# end

# accBuy = fetch(t1)
# accSell = fetch(t2)

# println("accBuy: ", mk_int_decrypt_3gen(secret_keys, accBuy, WIDTH))
# println("accSell: ", mk_int_decrypt_3gen(secret_keys, accSell, WIDTH))


# sellGRTbuy = mk_grt_3gen(bk, ks, accSell, accBuy, one, WIDTH)

# total1 = Array{MKLweSample}(undef, WIDTH)
# total2 = Array{MKLweSample}(undef, WIDTH)
# totalTmp = Array{MKLweSample}(undef, WIDTH)

# # println("num threads: ", Threads.nthreads())

# # Threads.@threads for i = 1:WIDTH
# #     # id = Threads.threadid()
# #     Threads.lock(spinlock)
# #     total1[i] = mk_gate_mux_3gen(bk, ks, sellGRTbuy, accBuy[i], accSell[i])
# #     Threads.unlock(spinlock)
# #     # println("id: ", id, "total_t1: ", mk_decrypt_3gen(secret_keys, total_t1[i]))
# # end

# # for i = 1:WIDTH
# #     println("total_t1: ", mk_decrypt_3gen(secret_keys, total1[i]))
# # end

# # total2 = total1

# # for i = 1:WIDTH
# #     println("total_t2: ", mk_decrypt_3gen(secret_keys, total2[i]))
# # end

# # println()

# for i = 1:WIDTH
# total1[i] = mk_gate_mux_3gen(bk, ks, sellGRTbuy, accBuy[i], accSell[i])
# total2[i] = total1[i]
# end

# for i = 1:WIDTH
# println("total1: ", mk_decrypt_3gen(secret_keys, total1[i]))
# end
# for i = 1:WIDTH
# println("total2: ", mk_decrypt_3gen(secret_keys, total2[i]))
# end

# t3 = @spawnat proc_ids[3] begin
# m = size(ord.buy, 1)
# println("m: ", m)
# buy = []

# for i = 1:m
# ordLeq = mk_leq_3gen(bk, ks, ord.buy[i], total1, one, WIDTH)
# res = Array{MKLweSample}(undef, WIDTH)

# for j = 1:WIDTH
# res[j] = mk_gate_mux_3gen(bk, ks, ordLeq, ord.buy[i][j], total1[j])
# end

# totalTmp = mk_sub_3gen(bk, ks, total1, res, one, WIDTH)

# for j = 1:WIDTH
# total1[j] = mk_copy_3gen(totalTmp[j])
# end

# # push!(resOrd.buy, res)
# push!(buy, res)
# end

# println("buy : ", mk_int_decrypt_3gen(secret_keys, buy[1], WIDTH))
# return buy
# end

# t4 = @spawnat proc_ids[4] begin
# n = size(ord.sell, 1)
# println("n: ", n)
# sell = []

# for i = 1:n
# ordLeq = mk_leq_3gen(bk, ks, ord.sell[i], total2, one, WIDTH)
# res = Array{MKLweSample}(undef, WIDTH)

# for j = 1:WIDTH
# res[j] = mk_gate_mux_3gen(bk, ks, ordLeq, ord.sell[i][j], total2[j])
# end

# totalTmp = mk_sub_3gen(bk, ks, total2, res, one, WIDTH)

# for j = 1:WIDTH
# total2[j] = mk_copy_3gen(totalTmp[j])
# end

# push!(sell, res)
# end

# println("sell : ", mk_int_decrypt_3gen(secret_keys, sell[1], WIDTH))
# return sell
# end

# # Wait for both tasks to complete
# @sync for t in (t3, t4)
# wait(t)
# end

# buy = fetch(t3)
# sell = fetch(t4)

# println("buy : ", mk_int_decrypt_3gen(secret_keys, buy[1], WIDTH))
# println("sell : ", mk_int_decrypt_3gen(secret_keys, sell[1], WIDTH))

# resOrd.buy = buy
# resOrd.sell = sell

# end