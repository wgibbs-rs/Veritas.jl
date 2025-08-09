module Context


"""
Contains information on the current running program, such as
the provided files, flags, and other information needed globally.
"""
struct ProgramContext
    input_files::Vector{String}         # A list of input file names
    input_file_asts::Vector{Expr}       # The AST associated with each input file
    smt_lib_encodings::Vector{String}   # The SMT-LIB encodings created for each file
    print_smt::Bool                     # Should the SMT-LIB be output to a file after encoding
    ProgramContext() = new(String[])
end # struct ProgramContext


end # module Context