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

let type_mismatch_numeric loc found =
  Error.error loc "type mismatch: expected a numeric, found %s" (T.show_ty found)
  
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
  | A.BinaryExp bexp -> set tref (check_bin_exp env pos bexp)
  | A.NegativeExp lexp -> set tref (check_neg_exp env lexp)
  | A.ExpSeq seq -> set tref (check_exp_seq env seq)
  | A.IfExp exp -> set tref (check_if_exp env exp)
  | A.WhileExp exp -> set tref (check_while_exp env exp)
  | A.BreakExp -> set tref (check_break_exp env pos)
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
  | _ -> Error.fatal "unimplemented"

and check_bin_exp env pos (expl, op, expr) =
  match op with
  | Plus
  | Minus
  | Times
  | Div
  | Mod
  | Power ->
    (match check_exp env expl with
    | T.INT
    | T.REAL ->
      (match check_exp env expr with
      | T.INT
      | T.REAL -> T.BOOL
      | t -> type_mismatch_numeric (loc expr) t)
    | t -> type_mismatch_numeric (loc expl) t)
  | Equal
  | NotEqual ->
    compatible (check_exp env expr) (check_exp env expl) pos;
    T.BOOL
  | GreaterThan
  | GreaterEqual
  | LowerThan
  | LowerEqual ->
    (match check_exp env expl with
    | T.INT
    | T.REAL ->
      (match check_exp env expr with
      | T.INT
      | T.REAL -> T.BOOL
      | t -> type_mismatch_numeric (loc expr) t)
    | T.STRING ->
      (match check_exp env expr with
      | T.STRING -> T.BOOL
      | t -> type_mismatch (loc expr) T.STRING t)
    | t -> Error.error (loc expl) "%s is incompatile with relational operators" (T.show_ty t))
  | And
  | Or ->
    (match check_exp env expl, check_exp env expr with
    | T.BOOL, T.BOOL -> T.BOOL
    | T.BOOL, t -> type_mismatch (loc expr) T.BOOL t
    | t, _ -> type_mismatch (loc expl) T.BOOL t)
  | _ -> Error.fatal "unimplemented"

and check_neg_exp env lexp =
  match check_exp env lexp with
  | T.INT -> T.INT
  | T.REAL -> T.REAL
  | t -> type_mismatch_numeric (loc lexp) t

and check_exp_seq env seq =
  match seq with
  | [] -> T.VOID
  | x::[] -> check_exp env x
  | x::xs ->
    ignore (check_exp env x);
    check_exp_seq env xs

and check_if_exp env (cond_exp, then_exp, else_exp) =
  compatible (check_exp env cond_exp) T.BOOL (loc cond_exp);
  let then_ty = check_exp env then_exp in
  match else_exp with
  | Some exp ->
    compatible (check_exp env exp) then_ty (loc exp);
    then_ty
  | None -> T.VOID

and check_while_exp env (cond_exp, body_exp) =
  compatible (check_exp env cond_exp) T.BOOL (loc cond_exp);
  let env' = {env with inloop = true} in
  ignore (check_exp env' body_exp);
  T.VOID

and check_break_exp env pos =
  if env.inloop then
    T.VOID
  else
    Error.error pos "break outside loop"

let semantic program =
  check_exp Env.initial program
