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

let _julia_command : string = {|
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

let verbose = ref false

let output_rocq = ref false

let output_filename = ref ""

let input_files = ref []

let parse_arguments () =
  let n = Array.length Sys.argv in
  (if n <= 1 then (
    Output.help (); 
    exit 0)
  else
    let i = ref 1 in
    while !i < n do
      (match Sys.argv.(!i) with
      | "-h" | "-H" | "--help" -> Output.help (); exit 0
      | "-V" | "-v" | "--verbose" -> verbose := true
      | "-o" ->
        if !i < n - 1 then (
          output_rocq := true;
          output_filename := Sys.argv.(!i + 1);
          i := !i + 1
        ) else
          Output.fatal_error "-o option requires 1 argument" 1
      | _ -> 
        if Sys.file_exists Sys.argv.(!i) then
          input_files := Sys.argv.(!i) :: !input_files
        else
          Output.error ("no such file or directory: \'" ^ Sys.argv.(!i) ^ "\'"));
      i := !i + 1
    done);
  if List.length !input_files = 0 then
    Output.fatal_error "no input files" 1

let () =
  parse_arguments ();
  exit 0
