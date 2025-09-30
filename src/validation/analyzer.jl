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
module Analyzer

include("smtlib.jl")
using .SMTLIB

const VariableType = (
    :integer,
    :type_undef # A special type used when a variable's type is unknown.
)

function create_theorem(ast, ctx)
    encoding = "" # Generate the start of our theorem.
    while true
        break
    end
    return encoding
end
export create_theorem

# Returns a string result for a given tested function
function check_contract_sat(title, text)
    result = check_smt2(text)
    if result 
        # Function is satisfiable, so there is a value that can fail the condition.
        # Function is [BAD]
        return ""
    else
        # File is NOT satisfiable, meaning there is no possible input to fail the program.
        # file is [OK]
        return ""
    end
end
export check_sat_result

end # module Analyzer