(* semantic.ml *)

module A = Absyn
module S = Symbol
module T = Type

type entry = [%import: Env.entry]
type env = [%import: Env.env]

(* Obtain the location of an ast *)

let loc = Location.loc

(* Reporting errors *)

let undefined loc category id =
  Error.error loc "undefined %s %s" category (S.name id)

let misdefined loc category id =
  Error.error loc "%s is not a %s" (S.name id) category

let type_mismatch loc expected found =
  Error.error loc "type mismatch: expected %s, found %s" (T.show_ty expected) (T.show_ty found)

(* Searhing in symbol tables *)

let look env category id pos =
  match S.look id env with
  | Some x -> x
  | None -> undefined pos category id

let tylook tenv id pos =
  look tenv "type" id pos

let varlook venv id pos =
  match look venv "variable" id pos with
  | VarEntry t -> t
  | FunEntry _ -> misdefined pos "variable" id

let funlook venv id pos =
  match look venv "function" id pos with
  | VarEntry _ -> misdefined pos "function" id
  | FunEntry (params, result) -> (params, result)

(* Type compatibility *)

let compatible ty1 ty2 pos =
  if not (T.coerceable ty1 ty2) then
    type_mismatch pos ty2 ty1

(* Set the value in a reference of optional *)

let set reference value =
  reference := Some value;
  value

(* Checking expressions *)

let rec check_exp env (pos, (exp, tref)) =
  match exp with
  | A.BoolExp _                         -> set tref T.BOOL
  | A.IntExp  _                         -> set tref T.INT
  | A.RealExp _                         -> set tref T.REAL
  | A.StringExp _                       -> set tref T.STRING
  | A.LetExp (decs, body)               -> check_exp_let env pos tref decs body
  | A.VarExp value                      -> check_var env value tref
  | A.AssignExp (var, value)            -> compatible (check_var env var tref) (check_exp env value) pos; set tref T.VOID
  | A.BinaryExp (left, op, right)       -> check_op env pos left op right tref
  | _                                   -> Error.fatal "unimplemented"

and check_op env pos left operator right tref =
  let l = check_exp env left in
  let r = check_exp env right in
  match operator with
  | A.Plus | A.Minus | A.Times | A.Div | A.Mod | A.Power -> 
    begin 
      match l, r with
      | T.INT, T.INT -> set tref T.INT
      | T.REAL, T.INT | T.INT, T.REAL | T.REAL, T.REAL -> set tref T.REAL
      | _ -> type_mismatch pos l r
    end
  | A.Equal | A.NotEqual ->
    compatible l r pos;
    set tref T.BOOL
  | A.GreaterThan | A.GreaterEqual | A.LowerThan | A.LowerEqual -> 
    begin
      match l, r with
      | T.BOOL, _ | _, T.BOOL | T.VOID, _ | _, T.VOID -> type_mismatch pos l r
      | T.INT, T.INT | T.REAL, T.INT | T.INT, T.REAL | T.REAL, T.REAL -> set tref T.BOOL
      | _ -> compatible l r pos; set tref T.BOOL
    end
  | A.Or | A.And -> 
    begin
      match l, r with
      | T.BOOL, T.BOOL -> set tref T.BOOL
      | T.BOOL, _ -> type_mismatch pos l r
      | _ -> type_mismatch pos T.BOOL l 
    end
  | _ -> Error.fatal "Unimplemented"

and check_var env (pos, var) tref = 
  match var with
  | A.SimpleVar value -> set tref (varlook env.venv value pos)
  | _                 -> Error.fatal "unimplemented"

and check_exp_let env pos tref decs body =
  let env' = List.fold_left check_dec env decs in
  let tbody = check_exp env' body in
  set tref tbody

(* Checking declarations *)

and check_dec_var env pos ((name, type_opt, init), tref) =
  let tinit = check_exp env init in
  let tvar =
    match type_opt with
    | Some tname ->
       let t = tylook env.tenv tname pos in
       compatible tinit t (loc init);
       t
    | None -> tinit
  in
  ignore (set tref tvar);
  let venv' = S.enter name (VarEntry tvar) env.venv in
  {env with venv = venv'}

and check_dec env (pos, dec) =
  match dec with
  | A.VarDec x -> check_dec_var env pos x
  | _ -> Error.fatal "unimplemented"

let semantic program =
  check_exp Env.initial program
