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

let rec exists elem lst =
  match lst with
  | [] -> false
  | head::tail -> elem = head || exists elem tail

let rec dup_exists lst =
  match lst with
  | [] -> false
  | head::tail -> (exists head tail) || dup_exists lst

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
  | A.NegativeExp value                 -> check_negative env pos value tref
  | A.ExpSeq (explist)                  -> check_sequence env explist tref
  | A.IfExp (cond, athen, aelse)        -> check_if_else env pos cond athen aelse tref
  | A.WhileExp (cond, body)             -> check_while env pos cond body tref
  | A.CallExp (name, args)              -> check_call env pos name args tref
  | A.BreakExp                          -> check_break env pos tref
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
  | _ -> type_mismatch pos l r

and check_negative env pos value tref = 
  let v = check_exp env value in
    match v with
    | T.REAL -> set tref T.REAL
    | T.INT -> set tref T.INT
    | _ -> type_mismatch pos T.INT v

and check_sequence env explist tref =
  match explist with
  | [] -> set tref T.VOID
  | elem::[] -> set tref (check_exp env elem)
  | _::list -> check_sequence env list tref

and check_if_else env pos cond athen aelse tref = 
  let c = check_exp env cond in
    match c with
    | T.BOOL -> 
    let t = check_exp env athen in
      begin
        match aelse with
        | Some value -> 
          let e = check_exp env value in
            compatible e t pos; 
            set tref t
        | None -> set tref T.VOID
      end
    | _ -> type_mismatch pos T.BOOL c

and check_while {venv; tenv; inloop} pos cond body tref =
  let c = check_exp {venv; tenv; inloop} cond in
    match c with
    | T.BOOL -> 
      ignore (check_exp {venv; tenv; inloop = true} body);
      set tref T.VOID
    | _ -> type_mismatch pos T.BOOL c

and check_break {venv; tenv; inloop} pos tref = 
  match inloop with
  | true -> set tref T.VOID
  | _ -> Error.error pos "break outside of loop"

and check_var env (pos, var) tref = 
  match var with
  | A.SimpleVar value -> set tref (varlook env.venv value pos)
  | _                 -> Error.fatal "unimplemented"

and check_exp_let env pos tref decs body =
  let env' = List.fold_left check_dec env decs in
  let tbody = check_exp env' body in
  set tref tbody

and check_call env pos name args tref = 
  let (params, rtype) = funlook env.venv name pos in
  if (List.length params) <> (List.length args)
    then 
      Error.error pos "incorrect argument number for function"
    else 
      check_call_types env pos params args; 
      set tref rtype; 

and check_call_types env pos params body =
  match params, body with
  | [], [] -> ()
  | (p::ptail, b::btail) -> compatible (check_exp env b) p pos; check_call_types env pos ptail btail;
  | _ -> Error.fatal "unexpected error"

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

and check_dec_fun env pos f =
  let env' = first_stage_cf env pos f in
  second_stage_cf env' pos f;
  env'

and check_params env pos params acc =
  match params with
  | [] -> acc
  | (_, ptype)::tail -> check_params env pos tail ((tylook env.tenv ptype pos)::acc)
  
and first_stage_cf env pos ((funcid, params, returntype, body), tref) =
  if dup_exists params 
  then
    Error.error pos "duplicated parameters"
  else
    let ptypes = check_params env pos params [] in
    let rtype = tylook env.tenv returntype pos in
    let venv' = S.enter funcid (FunEntry (ptypes, rtype)) env.venv in
      ignore (set tref rtype);
      {env with venv = venv'}

and second_stage_cf env pos ((funcid, params, returntype, body), tref) = 
  let (_,ftype) = funlook env.venv funcid pos in
  let env' = add_to_fenv env pos params in
    compatible ftype (check_exp env' body) pos

and add_to_fenv env pos params =
  match params with
  | [] -> env
  | ((pid, ptype))::tail -> 
    let ptype' = tylook env.tenv ptype pos in
    let venv' = S.enter pid (VarEntry ptype') env.venv in
    let env' = {env with venv=venv'} in
    add_to_fenv env' pos tail

and check_dec env (pos, dec) =
  match dec with
  | A.VarDec x -> check_dec_var env pos x
  | A.FunDec f -> check_dec_fun env pos f
  | _ -> Error.fatal "unimplemented"

let semantic program =
  check_exp Env.initial program
