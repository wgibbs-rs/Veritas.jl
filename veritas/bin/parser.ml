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

let parser_script : string = {|
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

let parse_julia_input_files (files : string list) : string =
  (* Create a temporary file for the Julia script *)
  let temp_script = Filename.temp_file "julia_parser_" ".jl" in
  
  try
    (* Write the parser_script content to the temporary file *)
    let oc = open_out temp_script in
    output_string oc parser_script;
    close_out oc;
    
    (* Build the command with julia and all file arguments *)
    let cmd = 
      "julia " ^ temp_script ^ " " ^ 
      (String.concat " " (List.map Filename.quote files))
    in
    
    (* Execute the command and capture output *)
    let ic = Unix.open_process_in cmd in
    let buf = Buffer.create 1024 in
    
    (* Read all output *)
    (try
      while true do
        Buffer.add_channel buf ic 1
      done
    with End_of_file -> ());
    
    let result = Buffer.contents buf in
    let status = Unix.close_process_in ic in
    
    (* Clean up temporary file *)
    Sys.remove temp_script;
    
    (* Check exit status and return result *)
    match status with
    | Unix.WEXITED 0 -> result
    | Unix.WEXITED n -> 
        failwith (Printf.sprintf "Julia script exited with code %d" n)
    | Unix.WSIGNALED n -> 
        failwith (Printf.sprintf "Julia script killed by signal %d" n)
    | Unix.WSTOPPED n -> 
        failwith (Printf.sprintf "Julia script stopped by signal %d" n)
  
  with e ->
    (* Ensure cleanup even if an exception occurs *)
    (try Sys.remove temp_script with _ -> ());
    raise e