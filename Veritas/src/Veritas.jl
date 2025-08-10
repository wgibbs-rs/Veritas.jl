module Veritas


include("Output.jl")



"""
Contains information on the current running program, such as
the provided files, flags, and other information needed globally.
"""
mutable struct ProgramContext
    input_files::Vector{String}         # A list of input file names
    input_file_asts::Vector{Expr}       # The AST associated with each input file
    smt_lib_encodings::Vector{String}   # The SMT-LIB encodings created for each file
    print_smt::Bool                     # Should the SMT-LIB be output to a file after encoding
    ProgramContext() = new(String[], Expr[], String[], false)
end # struct ProgramContext




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
    ctx = ProgramContext()

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
Parse the provided files, recording their ASTs. These recorded binary
trees will later be used to generate SMT-LIB, the language used in
static verifiers like Veritas.

This function will also check that the provided files exist. If not,
it will throw a fatal error. 

Note: Should this function throw a fatal error, or continue without that file?
"""
function parse_files(ctx)
    for file in ctx.input_files
        try
            contents = read(file, String)
            ast = Meta.parse(contents)
            push!(ctx.input_file_asts, ast)
        catch e
            fatal_error(string(e))
        end
    end
    
    return ctx;
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
    ctx::ProgramContext = parse_arguments(args)

    # Generate ASTs
    ctx = parse_files(ctx)


end # function main


main(ARGS)

end # module Veritas