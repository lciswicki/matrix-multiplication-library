# Łukasz Ciświcki

module blocksys
    using SparseArrays
    export gauss_method

    """
    Imports data from file to make the A vector\n
        Arguments:
            file_path: path to the data file
        Returns:
            A:  parameters matrix
            n:  size of A matrix
            l:  size of a block matrix
    """
    function read_A(file_path)
        n::Int = 0
        l::Int = 0
        I = Vector{Int}([])
        J = Vector{Int}([])
        V = Vector{Float64}([])

        file = open(file_path, "r")
        line = readline(file)
        words = split(line, " ")

        n = parse(Int, words[1])
        l = parse(Int, words[2])
        
        while(!eof(file))
            line = readline(file)
            words = split(line, " ")
            push!(I, parse(Int, words[1]))
            push!(J, parse(Int, words[2]))
            push!(V, parse(Float64, words[3]))
            # println(line)
        end

        A = sparse(I, J, V, n, n)

        return A, n, l
    end


    """
    Imports data from file to make the B vector\n
        Arguments:
            file_path: path to the data file
        Returns:
            B:  right-side vector
    """
    function read_B(file_path)
        n::Int = 0
        B = Vector{Float64}([])

        file = open(file_path, "r")
        line = readline(file)
        words = split(line, " ")

        n = parse(Int, words[1])
        
        while(!eof(file))
            line = readline(file)
            words = split(line, " ")
            push!(B, parse(Float64, words[1]))
        end

        return B
    end


    """
    Creates a right-side vector based on the x vector interpreted as "ones"\n
        Arguments:
            A: parameters matrix
        Returns:
            B: right-side vector
    """
    function create_B(A::SparseMatrixCSC{Float64, Int64})
        X = ones(size(A, 2))
        B = A * X
        return B
    end


    """
    Saves the resulting x vector to a file\n
        Arguments:
            file_name: path to the output file 
            x: vector to be saved
            relative_err: relative error to be saved (optional)
    """
    function write_to_file(file_name::String, x::Vector{Float64}, relative_err::Float64=0.0)
        open("./results/" * file_name, "w") do file
            if(relative_err != 0.0)
                write(file, "$relative_err\n")
            end
            for value in x
                write(file, "$value\n")
            end
        end
    end


    """
    Solves matrix multiplication using the Gauss algorithm\n
        Arguments:
            path_A: path to a file with the parameter matrix B
            path_B: path to a file with the right-side vector B
            partial_main: if enabled program uses a version of the algorithm partially selecting the main element (optional)
            counter: if enabled program counts iterations and returns more complex result
        Returns:
            X: resulting vector
            operations: number of performed iterations (optional, enabled by counter::Bool argument)
    """
    function gauss_method(path_A::String, path_B=nothing, partial_main::Bool=false, counter::Bool=false)
        A, n, l = blocksys.read_A(path_A)

        # counts operations used only to solve the matrix
        operations = 0

        if isnothing(path_B)
            B = create_B(A)
        else
            B = blocksys.read_B(path_B)
        end
    
        # display(A)
        
        # normal Gauss Elimination precedure
        if !partial_main
            for k = 1:n-1
                # number of elements left to eliminate
                # there's no need to iterate after the A submatrix ends
                to_elimin = k + (l - k % l)
                for i in (k + 1):to_elimin
                    if(A[k, k] == 0)
                        print("Error: division by '0'")
                        return
                    end
                    z = A[i, k] / A[k, k]
                    A[i, k] = 0.0
                    # for j = k+1:n
                    for j in (k + 1):min(n, k + l)
                        A[i, j] -= z * A[k, j]
                        operations += 1
                    end
                    B[i] -= z * B[k]
                end
            end
    
            # # solve backwards
            X = zeros(Float64, n)
            
            for k = n:-1:1
                sum = 0.0
                # for j = k+1:n
                for j in (k + 1):min(n, k + l)
                    sum += A[k, j] * X[j]
                    # coumputing complexity
                    
                end
                X[k] = (B[k] - sum) / A[k, k]
            end
    

        #  Gauss Elimination with choosing a main element
        else
            perm = [1:n;]
        
            # finding the right permutation
            for k = 1:n-1
                # number of elements left to eliminate
                # there's no need to iterate after the A submatrix ends
                to_elimin = k + (l - k % l)
                # row with maximum element
                max_row = k
                max_value = abs(A[k, k])

                for i = k:to_elimin
                    if abs(A[k, perm[i]]) > max_value
                        max_value = abs(A[k, perm[i]])
                        max_row = i
                    end
                end

                perm[k], perm[max_row] = perm[max_row], perm[k]
                
                # now starting the process of elimination
                # for i = k+1:to_elimin
                    
                for i in (k + 1):to_elimin
                    z = A[perm[i], k] / A[perm[k], k]
                    A[perm[i], k] = 0.0
        
                    for j in (k + 1):min(n, k + 2 * l)
                        A[perm[i], j] -= z * A[perm[k], j]
                        operations += 1
                    end
        
                    B[perm[i]] -= z * B[perm[k]]
                end
            end

            # solving in respect to the permutation
            X = zeros(Float64, n)

            for i in n:-1:1
                sum = 0.0
                for j in (i + 1):min(n, i + 2 * l)
                    sum += A[perm[i], j] * X[j]
                    # coumputing complexity
                    
                end
                X[i] = (B[perm[i]] - sum) / A[perm[i], i]
            end
            
        end

        err_sum = 0.0
        ones_vec = ones(n)

        for i = 1:n
            err_sum += abs(ones_vec[i] - X[i])
        end

        err = err_sum / n

        if counter
            return X, operations, err
        else
            return X
        end

    end


end

