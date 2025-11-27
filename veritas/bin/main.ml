(*
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
*)

(*
Veritas relies on a 3 step process.

1. Read, Parse, and Section Julia code into AST's for each verification condition.
2. Encode each verification condition AST into Rocq Gallina for future analysis
3. Pass this generated Gallina code to Rocq, and return the output to the user.
*)

(* Call Julia to parse our inputs. *)

let julia_command : string = {|
using JSON
function expr_to_dict(expr::Expr)
    return Dict(
        "head" => string(expr.head),
        "args" => [arg isa Expr ? expr_to_dict(arg) :
                   arg isa Symbol ? string(arg) :
                   arg for arg in expr.args]
    )
end
results = Vector{Any}()
for n in ARGS
    try
        push!(results, Dict("path" => n, "ast" => expr_to_dict(Meta.parse("begin\n" * read(n, String) * "\nend"))))
    catch e
        print("Error: " * string(e))
    end
end
print(JSON.json(results))
|}

let run_julia_parser (files : string list) : string =
  let files_arg = String.concat " " (List.map (Printf.sprintf "%S") files) in
  (* %S will correctly escape newlines and quotes *)
  let cmd = Printf.sprintf "julia -e %S -- %s" julia_command files_arg in
  let ic = Unix.open_process_in cmd in
  let output = In_channel.input_all ic in
  let _ = Unix.close_process_in ic in
  output

(* Example usage *)
let () =
  let result = run_julia_parser ["file1.jl"; "file2.jl"] in
  print_endline result

