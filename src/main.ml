open Format
open Lexing

let parse_only = ref false
let type_only = ref false
let dump = ref false
let dumpt = ref false

let ifile = ref ""

let set_var v s = v := s

let usage = "usage: mini-cpp [options] file.cpp"

let localisation pos =
  let l = pos.pos_lnum in
  let c = pos.pos_cnum - pos.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:\n"
    !ifile l (c-1) c

let localisation2 (pos1,pos2) =
  let l = pos1.pos_lnum in
  let c1 = pos1.pos_cnum - pos1.pos_bol + 1 in
  let c2 = pos2.pos_cnum - pos2.pos_bol + 1 in
  eprintf "File \"%s\", line %d, characters %d-%d:\n"
    !ifile l c1 c2
  
let options = [
  "--parse-only", Arg.Set parse_only, "Stops after parsing of the input file.";
  "--type-only", Arg.Set type_only, "Stops after typechecking of the input file.";
  "--dump", Arg.Set dump, "Dump the AST after parsing.";
  "--dumpt", Arg.Set dumpt, "Dump the AST after typing."
  ]

let () =
  Arg.parse options (set_var ifile) usage;

  if !ifile = "" then (
    eprintf "No input file\n@?";
    exit 1);
  
  if not (Filename.check_suffix !ifile ".cpp") then (
    eprintf "Input files must have suffix .cpp\n@?";
    Arg.usage options usage;
    exit 1);
  let basename = Filename.chop_suffix !ifile ".cpp" in
  
  let f = open_in !ifile in
  let buf = Lexing.from_channel f in

  try
    let p = Parser.prog Lexer.token buf in
    close_in f;
    
    if !dump then Pretty.print_prog p;
    if not !parse_only then begin
      let p = Typing.prog p in
      if !dumpt then Pretty_typing.print_prog p;

      if not !type_only then begin
        let asm = Codegen.generate p in
        Mips.print_in_file (basename ^ ".s") asm
      end
    end
  with
    | Lexer.Lexing_error s ->
      localisation (Lexing.lexeme_start_p buf);
      eprintf "Lexical analysis error: %s@." s;
      exit 1
    | Parser.Error -> 
            localisation (Lexing.lexeme_start_p buf);
      eprintf "Parsing error.@.";
      exit 1
    | Typing.Error(msg) ->
      eprintf "Typing error (unknown location): %s@." msg;
      exit 2
    | Typing.LocError (loc, msg) ->
      localisation2 loc;
      eprintf "%s@." msg;
      exit 2
    | Codegen.Very_bad_error(msg) ->
      eprintf "Very bad error: %s@." msg;
      exit 3;
      
    | _ ->
      eprintf "Unexpected error...@.";
      exit 3
