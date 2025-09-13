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
module Output

"""
Print an error without cancelling the entire program.
Used for things like non-existant input files, bad flags, etc.
"""
function error(msg::String)
    println("veritas: \033[1;31merror:\033[0m $msg")
end

"""
Print an error and exit the application early.
Used for instances were no further progression is possible.
"""
function fatal_error(msg::String, code::Int=1)
    println("veritas: \033[1;31merror:\033[0m $msg")
    println("veritas: \033[1;31merror:\033[0m analysis failed")
    exit(code)
end

"""
Print a help message with usage instructions before exiting the program.
"""
function help()
    println("""
Usage: julia Veritas.jl <options> <files>

Veritas.jl Static Analyzer 0.0.0
Julia program analysis and verification tool.

Options:
    -h, --help          Show this help message and exit.
    -v, --version       Show analyzer version number.
    -dump-ast           Print generated Julia AST.
    -dump-smt           Print generated SMT-LIB text.

Examples:
    julia Veritas.jl input.jl           Analyze an input file.
    """)
    exit()
end

"""
Print the current version of Veritas.jl
"""
function version()
    println("Veritas.jl version 0.0.0")
    exit()
end

"""
Create an smt2 file for each file being analyzed in the format of

input.smt2

This file will contain the smt2 encodings created by Veritas.
"""
function put_output(ctx)
    for file in ctx.input_file_names
        output_name = splitext(filename)[1] * ".smt2"
    end
end

"""
Print Julia AST to the terminal, using indents to represent
the depth of node.
"""
function print_ast(ex, depth=0)
    indent = "\t" ^ depth
    if ex isa Expr
        println(indent, "Expr(:", ex.head, ")")
        for arg in ex.args
            print_ast(arg, depth + 1)
        end
    else
        println(indent, repr(ex))
    end
end

end # module Output