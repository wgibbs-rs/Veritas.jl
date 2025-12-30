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

(* Print an error message, and exit the program with a code. *)
let fatal_error msg code =
    Printf.printf "veritas: \027[1;31merror:\027[0m %s\n" msg;
    Printf.printf "veritas: \027[1;31merror:\027[0m analysis failed\n";
    exit code

(* Print an error message that does not terminate the program. *)
let error msg = 
    Printf.printf "veritas: \027[1;31merror:\027[0m %s\n" msg

(* Print a help message with usage instructions before exiting the program. *)
let help () =
    print_endline
        "Usage: veritas <options> <files>\n\
        \n\
        Veritas.jl Static Analyzer 0.0.0\n\
        Julia program analysis and verification tool.\n\
        \n\
        Options:\n\
                -h, --help          Show this help message and exit.\n\
                -v, --version       Show analyzer version number.\n\
                -o FILE             Output ROCQ Gallina text to a file.\n\
        \n\
        Examples:\n\
                veritas input.jl    Analyze an input file with Veritas annotations.\n"

(* Print the current version of Veritas.jl *)
let version () =
    print_endline "Veritas.jl version 0.0.0"
