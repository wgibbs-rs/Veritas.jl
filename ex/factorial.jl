# Example: The Factorial Function

@pre n >= 0
@post result >= 1  # intentionally successful postcondition
@post result < 0   # intentionally failing postcondition
function factorial(n::Integer)
    if n <= 1 
        return 1
    end
    return factorial(n - 1) * n
end