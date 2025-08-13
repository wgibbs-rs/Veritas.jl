module Encoder


# Returns the header of the SMT-LIB encoding.
function smt2_header()
    return """
(set-info :smt-lib-version 2.7)
(set-logic ALL)
"""
end # function smt2_header

# Returns the end-code of the SMT-LIB encoding.
function smt2_footer()
    return """
(check-sat)
(get-model)
"""
end #function smt2_footer



function encode(text, ctx)
    return ""
end


end # module Encoder