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
export smt2_comment

end # module SMTLIB