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
  | A.BoolExp _ -> set tref T.BOOL
  | A.IntExp  _ -> set tref T.INT
  | A.RealExp _ -> set tref T.REAL
  | A.StringExp _ -> set tref T.STRING
  | A.LetExp (decs, body) -> check_exp_let env pos tref decs body
  | A.CallExp (id, params) -> check_call_exp env pos tref id params
  | _ -> Error.fatal "unimplemented"

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
  | A.FunDec x ->
    let env' = check_dec_fun_1 env pos x in
    check_dec_fun_2 env' pos x;
    env'
  | _ -> Error.fatal "unimplemented"

and check_dec_fun_1 env pos ((id, params, ty, _), tref) =
  let ty_list = check_params env params []
  and fun_ty = tylook env.tenv ty pos in
  let venv' = S.enter id (FunEntry (ty_list, fun_ty)) env.venv in
  ignore (set tref fun_ty);
  {env with venv=venv'}

and check_dec_fun_2 env pos ((id, params, _, exp), _) =
  let (_, t) = funlook env.venv id pos in
  let env' = List.fold_left add_param env params in
  let body_ty = check_exp env' exp in
  compatible body_ty t pos;

(* Adiciona um parâmetro ao ambiente como variável local *)
and add_param env (pos, ((id, ty), _)) =
  let pty = tylook env.tenv ty pos in
  let venv' = S.enter id (VarEntry pty) env.venv in
  {env with venv = venv'}

(* Verifica se os parâmetros tem tipos válidos
   e se tem nome repetido. Retorna uma lista
   com os tipos dos parâmetros*)
and check_params env params analized =
  match params with
  | [] -> []
  | (pos, ((id, ty), tref))::xs ->
    if List.mem id analized then
      Error.error pos "redefinition of parameter %s" (fst id)
    else
      let pty = tylook env.tenv ty pos in
      ignore (set tref pty);
      pty :: (check_params env xs (id::analized))
  
and check_call_exp env pos tref id params =
  let (ps, ty) = funlook env.venv id pos
  and ty_list = List.map (check_exp env) params in
  let len_e = List.length ps
  and len_f = List.length ty_list
  and comp a b = compatible a b pos in (* TODO: posição correta*)
  if len_e > len_f then
    Error.error pos "Too few arguments, expected %d found %d" len_e len_f
  else if len_e < len_f then
    Error.error pos "Too many arguments, expected %d found %d" len_e len_f
  else
    List.iter2 comp ty_list ps;
    set tref ty

let semantic program =
  check_exp Env.initial program
