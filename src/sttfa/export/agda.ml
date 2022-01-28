module D = Core.Deps
open Ast

let sys = "agda"

let cur_md = ref ""

(* no files in arith_fermat are using them but we still might get new files using them in the future *)
let forbidden_id = ref ["abstract";"constructor";"data";"do";"eta-equality";"field";"forall";"hiding";
                        "import";"in";"inductive";"infix";"infixl";"infixr";"instance";"let";"macro";
                        "module";"mutual";"no-eta-equality";"open";"overlap";"pattern";"postulate";
                        "primitive";"private";"public";"quote";"quoteContext";"quoteGoal";"quoteTerm";
                        "record";"renaming";"rewrite";"Set";"syntax";"tactic";"unquote";"unquoteDecl";
                        "unquoteDef";"using";"variable";"where";"with"]

let unicnt = ref 0

let pp_level oc () = 
  incr unicnt;
  Format.fprintf oc "l%d" !unicnt

let pp_unipoly oc () =
  if !unicnt = 0 then () else
  begin
  let unis = List.init !unicnt succ in
  unicnt := 0;
  let pp_sep oc () = Format.fprintf oc " " in
  let pp_item oc = Format.fprintf oc "l%d" in
  Format.(fprintf oc "{%a : Level} -> " (pp_print_list ~pp_sep pp_item) unis)
  end

let sanitize id =
  Core.Systems.sanitizer Agda ToTarget id

let print_var oc id =
  Format.fprintf oc "%s" (sanitize id)

let rec print_list sep pp oc = function
  | [] -> Format.fprintf oc ""
  | [x] -> Format.fprintf oc "(%a)" pp x
  | x::t -> Format.fprintf oc "(%a)%s%a" pp x sep (print_list sep pp) t

let print_dep oc dep =
  Format.fprintf oc "import %s\n" (sanitize dep)

let print_name oc (md,id) =
  let id = sanitize id in
  if !cur_md = md then
    Format.fprintf oc "%s" id
  else
    Format.fprintf oc "%s.%s" (sanitize md) id

let rec print_arity oc arity =
  if arity = 0 then
    Format.fprintf oc "Set %a" pp_level ()
  else
    Format.fprintf oc "Set %a -> %a" pp_level () print_arity (arity-1)

let rec print__ty oc = function
  | TyVar(var) ->
    Format.fprintf oc "%a" print_var var
  | Arrow(_tyl,_tyr) ->
    Format.fprintf oc "%a -> %a" print__ty_wp _tyl print__ty _tyr
  | TyOp(tyOp, []) ->
    Format.fprintf oc "%a" print_name tyOp
  | TyOp(tyOp, _tys) ->
    Format.fprintf oc "%a %a" print_name tyOp (print_list " " print__ty) _tys
  | Prop -> Format.fprintf oc "Set %a" pp_level ()

and print__ty_wp fmt _ty =
  match _ty with
  | TyVar _
  | Prop
  | TyOp _ -> print__ty fmt _ty
  | Arrow _ -> Format.fprintf fmt "(%a)" print__ty _ty

let rec print_ty oc = function
  | ForallK(var, ty) ->
    Format.fprintf oc "(%a : Set %a) -> %a" print_var var pp_level () print_ty ty
  | Ty(_ty) -> print__ty oc _ty

let print_poly_ty oc ty =
  let tystr = Format.asprintf "%a" print_ty ty in
  Format.fprintf oc "%a%s" pp_unipoly () tystr

let rec print__te oc = function
  | TeVar(var) ->
    Format.fprintf oc "%a" print_var var
  | Abs(var,_ty,_te) ->
    Format.fprintf oc "λ(%a : %a) -> %a" print_var var print__ty_wp _ty print__te _te
  | App(Abs _ as _tel,_ter) ->
    Format.fprintf oc "((%a) %a)" print__te _tel print__te_wp _ter
  | App(_tel,_ter) ->
    Format.fprintf oc "%a %a" print__te _tel print__te_wp _ter
  | Forall(var,_ty,_te) ->
    Format.fprintf oc "forall (%a : %a) -> %a" print_var var print__ty_wp _ty print__te _te
  | Impl(_tel,_ter) ->
    Format.fprintf oc "%a -> %a" print__te_wp _tel print__te _ter 
  | AbsTy(var, _te) ->
    Format.fprintf oc "λ(%a : Set %a) -> %a" print_var var pp_level () print__te _te
  | Cst(cst, []) ->
    Format.fprintf oc "%a" print_name cst
  | Cst(cst, _tys) ->
    Format.fprintf oc "%a %a" print_name cst (print_list " " print__ty) _tys

and print__te_wp fmt _te =
  match _te with
  | TeVar _
  | Cst(_,[]) -> Format.fprintf fmt "%a" print__te _te
  | _ -> Format.fprintf fmt "(%a)" print__te _te

let rec print_te oc = function
  | ForallP(var,te) -> (* Can actually be followed by other ForallP *)
    Format.fprintf oc "(%a : Set %a) -> %a" print_var var pp_level () print_te te 
  | Te(_te) -> print__te oc _te

let print_poly_te oc te =
  let testr = Format.asprintf "%a" print_te te in
  Format.fprintf oc "%a%s" pp_unipoly () testr


let rec printi__ty oc = function
  | TyVar(var) ->
    Format.fprintf oc "%a" print_var var
  | Arrow(_tyl,_tyr) ->
    Format.fprintf oc "%a -> %a" printi__ty_wp _tyl printi__ty _tyr
  | TyOp(tyOp, []) ->
    Format.fprintf oc "%a" print_name tyOp
  | TyOp(tyOp, _tys) ->
    Format.fprintf oc "%a %a" print_name tyOp (print_list " " printi__ty) _tys
  | Prop -> Format.fprintf oc "_" 

and printi__ty_wp fmt _ty =
  match _ty with
  | TyVar _
  | Prop
  | TyOp _ -> printi__ty fmt _ty
  | Arrow _ -> Format.fprintf fmt "(%a)" printi__ty _ty

let rec printi__te oc = function
  | TeVar(var) ->
    Format.fprintf oc "%a" print_var var
  | Abs(var,_ty,_te) ->
    Format.fprintf oc "λ(%a : %a) -> %a" print_var var printi__ty_wp _ty printi__te _te
  | App(Abs _ as _tel,_ter) ->
    Format.fprintf oc "((%a) %a)" printi__te _tel printi__te_wp _ter
  | App(_tel,_ter) ->
    Format.fprintf oc "%a %a" printi__te _tel printi__te_wp _ter
  | Forall(var,_ty,_te) ->
    Format.fprintf oc "forall (%a : %a) -> %a" print_var var printi__ty_wp _ty printi__te _te
  | Impl(_tel,_ter) ->
    Format.fprintf oc "%a -> %a" printi__te_wp _tel printi__te _ter 
  | AbsTy(var, _te) ->
    Format.fprintf oc "λ(%a : _) -> %a" print_var var printi__te _te
  | Cst(cst, []) ->
    Format.fprintf oc "%a" print_name cst
  | Cst(cst, _tys) ->
    Format.fprintf oc "%a %a" print_name cst (print_list " " printi__ty) _tys

and printi__te_wp fmt _te =
  match _te with
  | TeVar _
  | Cst(_,[]) -> Format.fprintf fmt "%a" printi__te _te
  | _ -> Format.fprintf fmt "(%a)" printi__te _te

let rec printi_te oc = function
  | ForallP(var,te) -> (* Can actually be followed by other ForallP *)
    Format.fprintf oc "(%a : _) -> %a" print_var var printi_te te 
  | Te(_te) -> printi__te oc _te


let rec print_proof oc = function 
  | Assume(_,var) -> Format.fprintf oc "%a" print_var var
  | Lemma(name,_) -> Format.fprintf oc "%a" print_name name
  | Conv(_,proof,_) -> Format.fprintf oc "%a" print_proof proof
  | ImplE(_,left,right) -> Format.fprintf oc "(%a) (%a)" print_proof left print_proof right
  | ImplI(_,proof,var) ->
    let j' = judgment_of proof in
    let _,_te = TeSet.choose (TeSet.filter (fun (x,_) -> if x = var then true else false) j'.hyp) in
    Format.fprintf oc "λ(%a : _) -> (%a)" print_var var print_proof proof
  | ForallE(_,proof,_te) -> Format.fprintf oc "(%a) (%a)" print_proof proof printi__te _te
  | ForallI(_,proof,var) ->
    let j' = judgment_of proof in
    let _,_ty = List.find (fun (x,_) -> x = var) j'.te in
    Format.fprintf oc "λ(%a : _) -> %a" print_var var print_proof proof
  | ForallPE(_,proof,_ty) -> Format.fprintf oc "(%a) (%a)" print_proof proof print__ty _ty
  | ForallPI(_,proof,var) ->
    Format.fprintf oc "λ(%a : _) -> %a" print_var var print_proof proof

let print_item oc = function
  | Parameter(name,ty) ->
    Format.fprintf oc "postulate %a : %a@." print_name name print_poly_ty ty
  | Definition(name,ForallK(tyvar,ty),te) ->
    let ty = ForallK(tyvar,ty) in
    Format.fprintf oc "%a : %a@.%a = %a@.@." 
      print_name name print_poly_ty ty print_name name printi_te te
  | Definition(name,ty,te) ->
    Format.fprintf oc "%a : %a@.%a = %a@.@." print_name name print_poly_ty ty print_name name printi_te te
  | Axiom (name,te) ->
    Format.fprintf oc "postulate %a : %a@." print_name name print_poly_te te 
  | Theorem(name,ForallP(hyv,te),proof) ->
    let te = ForallP(hyv,te) in
    Format.fprintf oc "%a : %a@.%a = %a@.@." 
      print_name name print_poly_te te print_name name print_proof proof
  | Theorem(name,te,proof) ->
    Format.fprintf oc "%a : %a@.%a = %a@.@." print_name name print_poly_te te print_name name print_proof proof
  | TypeDecl(tyop,arity) ->
    Format.fprintf oc "data %a : %a where@." print_name tyop print_arity arity
  | TypeDef (name,_,_) ->
    Format.fprintf oc "-- Type definition (for %a) not handled right now@." print_name name

(* Agda.Primitive needed for Level *)
let print_ast : Format.formatter -> ?mdeps:Ast.mdeps -> Ast.ast -> unit = fun fmt ?mdeps:_ ast ->
  cur_md := ast.md;
  Format.fprintf fmt "module %s where\nopen import Agda.Primitive\n" (sanitize !cur_md);
  D.QSet.iter (print_dep fmt) ast.dep;
  List.iter (print_item fmt) ast.items

(*
let print_meta_ast fmt meta_ast =
  let print_ast fmt ast =
    Format.fprintf fmt "module %s where\n" ast.md; (* You need to indent for a top-level module *)
    print_ast fmt ast;
  in
  List.iter (print_ast fmt) meta_ast

let to_string fmt = Format.asprintf "%a" fmt
*)

(* TODO : update it according to print_item *)
let string_of_item = function
  | Parameter((_,id),ty) ->
    let id = sanitize id in
    Format.asprintf "postulate %s : %a" id print_ty ty
  | Definition((_,id),ty,te) ->
    let id = sanitize id in
    Format.asprintf "%s : %a@.%s = %a" id print_ty ty id print_te te 
  | Axiom((_,id),te) ->
    let id = sanitize id in
    Format.asprintf "postulate %s : %a" id print_te te
  | Theorem((_,id),te,_) ->
    let id = sanitize id in
    Format.asprintf "%s : %a" id print_te te
  | TypeDecl((_,id),arity) ->
    let id = sanitize id in
    Format.asprintf "%s : %a" id print_arity arity
  | TypeDef _ -> failwith "[AGDA] Type definitions not handled right now" 
