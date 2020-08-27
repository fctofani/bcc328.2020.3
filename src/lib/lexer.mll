{
  module L = Lexing

  type token = [%import: Parser.token] [@@deriving show]

  let set_filename lexbuf fname =
    lexbuf.L.lex_curr_p <-
      { lexbuf.L.lex_curr_p with L.pos_fname = fname }

  let illegal_character loc char =
    Error.error loc "illegal character '%c'" char
}
rule token = parse
  | [' ' '\t']+                           { token lexbuf }
  | ['\n']                                { L.new_line lexbuf; token lexbuf }
  | ['0'-'9']+ as value                   { INT (int_of_string value) }
  | "true"                                { BOOL true }
  | "false"                               { BOOL false }
  | eof                                   { EOF }
  | _                                     { illegal_character (Location.curr_loc lexbuf) (L.lexeme_char lexbuf 0) }
