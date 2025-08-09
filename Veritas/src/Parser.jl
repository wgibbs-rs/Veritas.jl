module Parser

include("Context.jl")
using .Context


function parse_file(file_name)
    println("Parsing a file...")
    # Here, we'll use Meta.parse and traverse the code provided 
    # to make sure it does not include unsupported features, etc.
end

end # module Parser