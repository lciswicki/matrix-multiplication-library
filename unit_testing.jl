# Łukasz Ciświcki

using SparseArrays
using Test
include("blocksys.jl")

# Proving that my program works correctly

# unit tests for gauss
@testset "problem size: 10,000" begin
    path_A = "tests/Dane10000_1_1/A.txt"
    path_B = "tests/Dane10000_1_1/b.txt"
    result = ones(10000)
    @test isapprox(blocksys.gauss_method(path_A, path_B), result)
    @test isapprox(blocksys.gauss_method(path_A, path_B, true), result)
end

@testset "problem size: 50,000" begin
    path_A = "tests/Dane50000_1_1/A.txt"
    path_B = "tests/Dane50000_1_1/b.txt"
    result = ones(50000)
    @test isapprox(blocksys.gauss_method(path_A, path_B), result)
    @test isapprox(blocksys.gauss_method(path_A, path_B, true), result)
end


