module Veritas


include("Output.jl")
using .Output

include("Parser.jl")
using .Parser

include("Context.jl")
using .Context


"""
Parse arguments provided in the command line.

For now, a basic argument to Veritas.jl will be in the format of:

`veritas file1.jl file2.jl file3.jl`

and each file will be analyzed seperately, crossing only into other files,
even files that were not explicitly stated, when specifically required with
'using', 'import', or 'include()'.

NOTE: There are currently no flags, so all arguments are treated as files.

Returns a ProgramContext.
"""
function parse_arguments(args) 
    ctx = Context.ProgramContext()

    for arg in args
        if arg == "--print"
            ctx.print_smt = true;
        else 
            push!(ctx.input_files, arg)
        end
    end

    return ctx
end



"""
Main entry point for Veritas.jl.

This function performs the following steps:

1. Parses the command-line arguments.
2. Reads and parses the input file(s) into Julia ASTs using `Meta.parse(s::String)`.
3. Converts the generated AST's into SMT-LiB texts.
4. Passes the SMT-LiB texts to the analysis backend: Z3.
4. Returns or prints the analysis results.

"""
function main(args)
    
    # Take in arguments
    parse_arguments(args)

end # function main


main(ARGS) # call the main function when not wrapped into a binary.

end # module Veritas