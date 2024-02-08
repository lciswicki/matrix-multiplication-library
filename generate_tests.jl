using SparseArrays
using Plots
include("blocksys.jl")
include("matrixgen.jl")

# Measuring parameters as computations, time and memory usage
# and representing them in form of plots


# generate additional data
function generate_tests()
    for n = 5000:5000:50000
        l = 5
        ck = 1.0
        output_a = "./new_tests/" * "A_" * string(n) * ".txt"
        matrixgen.blockmat(n, l, ck, output_a)
    end
end


# tests number of iterations
function generate_operations(max)
    normal_time = Vector{Int}()
    partial_time = Vector{Int}()
    append!(normal_time, 0)
    append!(partial_time, 0)


    for n = 5000:5000:max
        print("[matrix size ", n ,"\t completion: ")
        path_A = "./new_tests/" * "A_" * string(n) * ".txt"
        append!(normal_time, blocksys.gauss_method(path_A, nothing, false, true)[2])
        append!(partial_time, blocksys.gauss_method(path_A, nothing, true, true)[2])
        print("yes]\n")
    end
    return normal_time, partial_time
end


# plots number of iterations
function plot_operations(normal_operations, partial_operations, max)
    x = [0:5000:max]
    # x = [0, 5000, 10000, 15000, 20000]
    plot(x, [normal_operations, partial_operations],
    title="Number of iterations for the Gauss methods",
    labels=["Normal Gauss Method" "Gauss Method with partial choosing"],
    formatter = :plain)
    savefig("./plots/operations")
end


# tests real time elapsed
function generate_time(max, reps::Int)
    normal_time = Vector{Float64}()
    partial_time = Vector{Float64}()

    append!(normal_time, 0)
    append!(partial_time, 0)

    for n = 5000:5000:max
        print("[matrix size ", n ,"\t completion: ")
        path_A = "./new_tests/" * "A_" * string(n) * ".txt"

        summ_normal = 0
        summ_partial = 0

        for x = 1:reps
            stats_normal = @timed blocksys.gauss_method(path_A, nothing, false, true)
            stats_partial = @timed blocksys.gauss_method(path_A, nothing, true, true)
            summ_normal += stats_normal.time
            summ_partial += stats_partial.time
        end

        append!(normal_time, round(summ_normal / reps, sigdigits=3))
        append!(partial_time, round(summ_partial / reps, sigdigits=3))

        print("yes]\n")
    end
    return normal_time, partial_time
end


# plots real time elapsed
function plot_time(normal_time, partial_time, max)
    x = [0:5000:max]
    # x = [0, 5000, 10000, 15000, 20000]
    plot(x, [normal_time, partial_time],
    title="Time of calculations for the Gauss methods",
    labels=["Normal Gauss Method" "Gauss Method with partial choosing"],
    formatter = :plain)
    savefig("./plots/times")
end


# tests number of bytes allocated
function generate_memory(max)
    normal_mem = Vector{Float64}()
    partial_mem = Vector{Float64}()

    append!(normal_mem, 0)
    append!(partial_mem, 0)

    for n = 5000:5000:max
        print("[matrix size ", n ,"\t completion: ")
        path_A = "./new_tests/" * "A_" * string(n) * ".txt"

        append!(normal_mem, @allocated blocksys.gauss_method(path_A, nothing, false, true))
        append!(partial_mem, @allocated blocksys.gauss_method(path_A, nothing, true, true))

        print("yes]\n")
    end
    return normal_mem, partial_mem
end


# plots number of bytes allocated
function plot_mem(normal_mem, partial_mem, max)
    x = [0:5000:max]
    # x = [0, 5000, 10000, 15000, 20000]
    plot(x, [normal_mem, partial_mem],
    title="Memory allocated by the Gauss methods",
    labels=["Normal Gauss Method" "Gauss Method with partial choosing"],
    formatter = :plain)
    savefig("./plots/mem")
end


# normal_op, choose_op = generate_operations(50000)
# plot_operations(normal_op, choose_op, 50000)

# normal_t, choose_t = generate_time(50000, 10)
# plot_time(normal_t, choose_t, 50000)

# normal_m, choose_m = generate_memory(50000)
# plot_mem(normal_m, choose_m, 50000)

A_path = "tests/Dane100000_1_1/A.txt"
results_normal = blocksys.gauss_method(A_path, nothing, false, true)
results_choose = blocksys.gauss_method(A_path, nothing, true, true)
blocksys.write_to_file("./normal10.txt", results_normal[1], results_normal[3])
blocksys.write_to_file("./choose10.txt", results_choose[1], results_choose[3])
