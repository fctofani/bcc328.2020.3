{
  module L = Lexing

  type token = [%import: Parser.token] [@@deriving show]

  let set_filename lexbuf fname =
    lexbuf.L.lex_curr_p <-
      { lexbuf.L.lex_curr_p with L.pos_fname = fname }

  let illegal_character loc char =
    Error.error loc "illegal character '%c'" char

  let comment_begin = ref L.dummy_pos

  let append_char str ch =
    str ^ (String.make 1 (Char.chr ch))

  let str_incr_linenum str lexbuf =
    String.iter (function '\n' -> L.new_line lexbuf | _ -> ()) str

  let illegal_escape loc sequence =
    Error.error loc "illegal escape sequence: %s" sequence

  let unterminated_string loc =
    Error.error loc "unterminated string"

}

let spaces = [' ' '\t']+
let digit = ['0'-'9']
let integer = digit+
let exponent = ['e' 'E'] ['+' '-']? integer
let real = integer ('.' integer exponent? | exponent)
let id = ['a'-'z''A'-'Z']['0'-'9''a'-'z''A'-'Z''_']*

rule token = parse
  | spaces            { token lexbuf }
  | '\n'              { L.new_line lexbuf; token lexbuf }
  | "{#"              { comment_begin := L.lexeme_start_p lexbuf; read_comment 0 lexbuf }
  | '#' [^'\n']*      { token lexbuf }
  | real as lxm       { LITREAL (float_of_string lxm) }
  | integer as lxm    { LITINT (int_of_string lxm) }
  | "true"            { LITBOOL true }
  | "false"           { LITBOOL false }
  | "+"               { PLUS }
  | "-"               { MINUS }
  | "*"               { TIMES }
  | "/"               { DIV }
  | "%"               { MOD }
  | "^"               { POW }
  | "="               { EQ }
  | "<>"              { NE }
  | ">"               { GT }
  | ">="              { GE }
  | "<"               { LT }
  | "<="              { LE }
  | "&&"              { AND }
  | "||"              { OR }
  | ":="              { ASSIGN }
  | '('               { LPAREN }
  | ')'               { RPAREN }
  | ','               { COMMA }
  | ';'               { SEMI }
  | ':'               { COLON }
  | "break"           { BREAK }
  | "do"              { DO }
  | "else"            { ELSE }
  | "end"             { END }
  | "if"              { IF }
  | "in"              { IN }
  | "let"             { LET }
  | "then"            { THEN }
  | "var"             { VAR }
  | "while"           { WHILE }
  | "function"        { FUNCTION }
  | id as lxm         { ID (Symbol.symbol lxm) }
  | '"'               { stringRule lexbuf.L.lex_start_p "" lexbuf }
  | eof               { EOF }
  | _                 { illegal_character (Location.curr_loc lexbuf) (L.lexeme_char lexbuf 0) }

and read_comment nested_count = parse
  | "{#"  { read_comment (nested_count+1) lexbuf }
  | "#}"  { if nested_count = 0 then
              token lexbuf
            else
              read_comment (nested_count-1) lexbuf
          }
  | '\n'  { L.new_line lexbuf; read_comment nested_count lexbuf }
  | eof   { Error.error (!comment_begin, L.lexeme_end_p lexbuf) "unterminated comment" }
  | _     { read_comment nested_count lexbuf }

and stringRule pos buf = parse
  | '"'                               { lexbuf.L.lex_start_p <- pos;
                                        LITSTRING buf
                                      }
  | "\\n"                             { stringRule pos (buf ^ "\n") lexbuf }
  | "\\t"                             { stringRule pos (buf ^ "\t") lexbuf }
  | "\\r"                             { stringRule pos (buf ^ "\r") lexbuf }
  | "\\b"                             { stringRule pos (buf ^ "\b") lexbuf }
  | "\\\""                            { stringRule pos (buf ^ "\"") lexbuf }
  | "\\\\"                            { stringRule pos (buf ^ "\\") lexbuf }
  | "\\" (digit digit digit as x)     { stringRule pos (append_char buf (int_of_string x)) lexbuf }
  | "\\" ([' ' '\t' '\n']+ as x) "\\" { str_incr_linenum x lexbuf;
                                        stringRule pos buf lexbuf
                                      }
  | "\\" ([' ' '\t' '\n']+ as x) "\\" { str_incr_linenum x lexbuf;
                                        stringRule pos buf lexbuf
                                      }
  | "\\" _ as x                       { illegal_escape (lexbuf.L.lex_start_p, lexbuf.L.lex_curr_p) x;
                                        stringRule pos buf lexbuf
                                      }
  | [^ '\\' '"']+ as x                { str_incr_linenum x lexbuf;
                                        stringRule pos (buf ^ x) lexbuf
                                      }
  | eof                               { unterminated_string (pos, lexbuf.L.lex_start_p);
                                        token lexbuf
                                      }