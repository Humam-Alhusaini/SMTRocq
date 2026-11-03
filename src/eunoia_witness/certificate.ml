(**************************************************************************)
(*     SMTCoq -- distributed under the terms of the CeCILL-C licence       *)
(**************************************************************************)

open Common

type literal = int
type clause = literal list
type clause_id = int
type lia_proof = RocqInterface.Micromega_plugin_Certificate.Mc.zArithProof list
type action =
  | Res of clause_id * clause_id * clause_id
  | CFalse of clause_id
  | BuildDef of clause_id * literal
  | BuildDef2 of clause_id * literal
  | BuildProj of clause_id * literal * int
  | EqTr of clause_id * literal * literal list
  | EqCgr of clause_id * literal * literal option list
  | EqCgrP of clause_id * literal * literal * literal option list
  | LiaMicromega of clause_id * clause * lia_proof
type command = { action : action; expected : clause }
type witness = {
  capacity : int;
  root_claims : (clause_id * clause) list;
  program : command list;
  conflict : clause_id;
}

let output = function
  | Res (p,_,_) | CFalse p | BuildDef (p,_) | BuildDef2 (p,_)
  | BuildProj (p,_,_) | EqTr (p,_,_) | EqCgr (p,_,_)
  | EqCgrP (p,_,_,_) | LiaMicromega (p,_,_) -> p
let reads = function Res (_,a,b) -> [a;b] | _ -> []
let canonical c = List.sort_uniq Int.compare c

(* State.C.resolve removes the first complementary pair in numeric order.
   Its no-pivot fallback is observable, even after a common prefix. *)
let rec resolve a b = match a,b with
  | [],_ | _,[] -> [0]
  | x::xs,y::ys ->
    if x = y then x :: resolve xs ys
    else if x lxor y = 1 then canonical (xs @ ys)
    else if x < y then x :: resolve xs b
    else y :: resolve a ys

let to_coq ~local ~step w =
  let open RocqInterface in
  let open CoqTerms in
  let int = mkInt in
  let ty = Lazy.force cint in
  let app c args = mkApp (c, Array.of_list args) in
  let list t f xs = List.fold_right
      (fun x tail -> app (Lazy.force ccons) [t;f x;tail]) xs
      (app (Lazy.force cnil) [t]) in
  let clause = list ty int in
  let option_ty = app (Lazy.force coption) [ty] in
  let option = function
    | None -> app (Lazy.force cNone) [ty]
    | Some l -> app (Lazy.force cSome) [ty;int l] in
  let act = function
    | Res (p,a,b) -> app (step "Res")
        [int p; mkArray (ty, [|int a;int b;int 0|])]
    | CFalse p -> app (step "CFalse") [int p]
    | BuildDef (p,l) -> app (step "BuildDef") [int p;int l]
    | BuildDef2 (p,l) -> app (step "BuildDef2") [int p;int l]
    | BuildProj (p,l,i) -> app (step "BuildProj") [int p;int l;int i]
    | EqTr (p,l,ls) -> app (step "EqTr") [int p;int l;clause ls]
    | EqCgr (p,l,ls) -> app (step "EqCgr")
        [int p;int l;list option_ty option ls]
    | EqCgrP (p,a,b,ls) -> app (step "EqCgrP")
        [int p;int a;int b;list option_ty option ls]
    | LiaMicromega (p,c,proof) -> app (step "LiaMicromega")
        [int p;clause c;list (Lazy.force micromega_coq_proofTerm)
          micromega_dump_proof_term proof] in
  let clause_ty = app (Lazy.force clist) [ty] in
  let pair_ty = app (Lazy.force cprod) [ty;clause_ty] in
  let root (id,c) = app (Lazy.force cpair) [ty;clause_ty;int id;clause c] in
  let command cmd = app (local "Command") [act cmd.action;clause cmd.expected] in
  app (local "Witness") [int w.capacity;list pair_ty root w.root_claims;
    list (local "command") command w.program;int w.conflict]
