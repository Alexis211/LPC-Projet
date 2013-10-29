open Format
open Lexing

let ifile = ref ""

let set_var v s = v := s

let usage = "usage: mini-cpp [options] file.cpp"

let localisation pos =
	let l = pos.pos_lnum in
	let c = pos.pos_cnum - pos.pos_bol + 1 in
	eprintf "File \"%s\", line %d, characters %d-%d:\n"
		!ifile l (c-1) c
	
let options = []

let () =
	Arg.parse options (set_var ifile) usage;

	if !ifile = "" then (
		eprintf "No input file\n@?";
		exit 1);
	
	if not (Filename.check_suffix !ifile ".cpp") then (
		eprintf "Input files must have suffix .cpp\n@?";
		Arg.usage options usage;
		exit 1);
	
	let f = open_in !ifile in
	let buf = Lexing.from_channel f in

	try
		while true do
			print_string (Pretty.token_str (Lexer.token buf));
			print_string "\n"
		done
	with
		| Lexer.End_of_file ->
			exit 0
		| Lexer.Lexing_error s ->
			localisation (Lexing.lexeme_start_p buf);
			eprintf "Lexical analysis error: %s@." s;
			exit 1
