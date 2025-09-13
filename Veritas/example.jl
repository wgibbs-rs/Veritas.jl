

# Asserts that for every input x and y,
@pre y != 0
@post divide * y = x
function divide(x, y)
    return x / y
end

# The trouble with functions like this is that X, Y, and result are all unknown
# types. Veritas will test treating X and Y as floating points, while stating that
# full testing is unavailable due to dynamic typing.