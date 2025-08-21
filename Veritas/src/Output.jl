
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
    exit(code)
end

"""
Create an smt2 file for each file being analyzed in the format of

input.jl.smt2

This file will contain the smt2 encodings created by Veritas.
"""
function put_output(ctx)

    for file in ctx.input_files

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