module VeritasAnnotations

export @pre, @post

macro pre(expr)
    return nothing
end

macro post(expr)
    return nothing
end

end # module VeritasAnnotations