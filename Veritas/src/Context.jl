module Context


"""
Contains information on the current running program, such as
the provided files, flags, and other information needed globally.
"""
struct ProgramContext
    input_files::Vector{String}
    print_smt::Bool
    ProgramContext() = new(String[])
end


end