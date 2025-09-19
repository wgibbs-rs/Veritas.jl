"""
ZLib License

Copyright (c) 2025 William Gibbs

This software is provided 'as-is', without any express or implied
warranty. In no event will the authors be held liable for any damages
arising from the use of this software.

Permission is granted to anyone to use this software for any purpose,
including commercial applications, and to alter it and redistribute it
freely, subject to the following restrictions:

1. The origin of this software must not be misrepresented; you must not
    claim that you wrote the original software. If you use this software
    in a product, an acknowledgment in the product documentation would be
    appreciated but is not required.

2. Altered source versions must be plainly marked as such, and must not be
    misrepresented as being the original software.

3. This notice may not be removed or altered from any source distribution.
"""
module Veritas

include("preprocess.jl")
using .Preprocess

include("output.jl")
using .Output

include("validation/analyzer.jl")
using .Analyzer

"""
Contains information on the current running program, such as
the provided files, flags, and other information needed globally.
"""
mutable struct ProgramContext
    input_file_names::Vector{String}    # A list of input file names
    input_file_asts::Vector{Expr}       # The AST associated with each input file
    smt2_encodings::Vector{String}      # The SMT-LIB encodings created for each file
    dump_smt::Bool                      # Should the SMT-LIB be output to a file after encoding
    dump_ast::Bool                      # Should Veritas print the Julia code to the terminal
    ProgramContext() = new(
        String[], 
        Expr[], 
        String[], 
        false, 
        false
    )
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
        if arg == "-h" || arg == "--help"
            Output.help()
        elseif arg == "-v" || arg == "--version"
            Output.version()
        elseif arg == "--dump-ast"
            ctx.dump_ast = true;
        elseif arg == "--dump-smt"
            ctx.dump_smt = true;
        else
            if startswith(arg, "-")
                fatal_error("option \"$arg\" is unknown.\n  use \"src/veritas.jl --help\" for a list of options.")
            else
                push!(ctx.input_file_names, arg)
            end
        end
    end
    return ctx
end

"""
Parse the provided files, recording their ASTs. These recorded binary
trees will later be used to generate SMT-LIB, the language used in
static verifiers like Veritas.
"""
function parse_files(ctx)
    for file in ctx.input_file_names
        try
            contents = "begin\n" * read(file, String) * "\nend"
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
5. Returns or prints the analysis results.
"""
function main(args)
    # Take in arguments
    ctx::ProgramContext = parse_arguments(args)

    # Generate ASTs
    ctx = parse_files(ctx)

    # Prepare each ast for encoding
    for i in eachindex(ctx.input_file_asts)
        ctx.input_file_asts[i] = clean(ctx.input_file_asts[i], ctx)
    end

    # encode each file to SMT-LIB
    for ast in ctx.input_file_asts
        model = create_model(ast, ctx)
        push!(ctx.smt2_encodings, model)
        if ctx.dump_ast
            Output.print_ast(ast)
        end
    end

    # If dumping the SMT-LIB encodings, we'll do that here, then exit.
    if ctx.dump_smt
        for i in 1:length(ctx.input_files)
            # create files and dump
        end
        exit()
    end

    # If not printing these encodings, we'll feed them to Z3 here... later.

    # Print the resulting outputs from Z3, cleanup, etc.

end # function main

main(ARGS)

end # module Veritas