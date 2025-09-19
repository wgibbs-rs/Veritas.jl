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
module SMTLIB

using Z3

function check_smt2(text::String)
    ctx = Context()
    asts = Z3.Libz3.Z3_parse_smtlib2_string(ctx.ctx, text, 0, C_NULL, C_NULL, 0, C_NULL, C_NULL)
    solver = Solver(ctx)
    for i in 1:Z3.Libz3.Z3_ast_vector_size(ctx.ctx, asts)
        ast = Z3.Libz3.Z3_ast_vector_get(ctx.ctx, asts, i)
        add(solver, ast)
    end
    return Z3.check(solver) == Z3.CheckResult(:sat)
end
export check_smt2

# Returns the header of the SMT-LIB encoding.
function smt2_header()
    return """\n
(set-info :smt-lib-version 2.7)
(set-info :source "Veritas.jl https://www.github.com/wgibbs-rs/veritas.jl")
(set-logic QF_LIA)
"""
end
export smt2_header

# Returns the end-code of the SMT-LIB encoding.
function smt2_footer()
    return "\n(exit)\n"
end
export smt2_footer

# Returns a line that can be added directly
function new_line(text)
    return "\n$text\n"
end
export new_line

end # module SMTLIB