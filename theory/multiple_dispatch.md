
To correctly analyze a language as dynamic as Julia, covering each of its dynamic elements is important to ensure code correctness. One major dynamic aspect of Julia is "multiple dispatch" where a function can be redefined with different arguments. Take the following code as an example:

```jl
function my_function(a, b)
    # do stuff
end
function my_function(a, b, c)
    # do something else
end
```

But Rocq can't handle that, and we can't easily make mathematical assertions about that. 

To solve this, we can combine the functions using an if statement, and treating their arguments as a single-input array.

```jl
function my_function(args)
    if length(args) == 2
        # do stuff with the two-argument function.
    else
        # do stuff with the three-argument function.
    end
end
```

What if the function are the same, but rely on seperate types? 
What if no argument is provided for the third argument?