open Common
open SmtAtom

type t = Truth | Identity | Trans | Congruence of int option list | Linear of Certificate.lia_proof
let lit = Form.to_lit
let neg l = l lxor 1
let units cs =
  let rec go acc = function
    | [] -> Some (List.rev acc)
    | [l]::rest -> go (l::acc) rest
    | _ -> None in go [] cs
let equality f =
  if not (Form.is_pos f) then None else
  match Form.pform f with
  | Fatom a -> (match Atom.atom a with Abop (BO_eq _,a,b) -> Some(a,b) | _ -> None)
  | _ -> None
let transitive goal premises =
  match equality goal with
  | None -> false
  | Some (a,b) ->
    let endpoint x y = Atom.equal x a && Atom.equal y b || Atom.equal x b && Atom.equal y a in
    let rec chain x y = function
      | [] -> endpoint x y
      | f::rest -> match equality f with
        | None -> false
        | Some (u,v) ->
          if Atom.equal y v then chain x u rest else
          if Atom.equal y u then chain x v rest else
          if Atom.equal x v then chain u y rest else
          if Atom.equal x u then chain v y rest else false in
    match premises with
    | [] -> Atom.equal a b
    | first::rest -> match equality first with None -> false | Some(x,y) -> chain x y rest
let congruent goal premises =
  let arguments a b = match Atom.atom a,Atom.atom b with
    | Auop(o,a),Auop(p,b) when o=p -> Some([a],[b])
    | Abop(o,a,b),Abop(p,c,d) when o=p -> Some([a;b],[c;d])
    | Aapp(f,xs),Aapp(g,ys) when indexed_op_index f=indexed_op_index g && Array.length xs=Array.length ys ->
      Some(Array.to_list xs,Array.to_list ys)
    | _ -> None in
  match equality goal with None -> None | Some(a,b) ->
  match arguments a b with None -> None | Some(xs,ys) ->
  let rec go acc xs ys = match xs,ys with
    | [],[] -> Some(List.rev acc)
    | x::xs,y::ys ->
      if Atom.equal x y then go (None::acc) xs ys else
      (match List.find_opt (fun f -> match equality f with
        | Some(a,b) -> Atom.equal a x && Atom.equal b y || Atom.equal b x && Atom.equal a y
        | None -> false) premises with
       | None -> None | Some f -> go (Some(lit f)::acc) xs ys)
    | _ -> None in
  match go [] xs ys with
  | Some args when Certificate.canonical (List.filter_map Fun.id args)=Certificate.canonical (List.map lit premises) -> Some args
  | _ -> None
(* Atomic arithmetic clauses avoid Boolean CNF search entirely. Keep Boolean
   expansion and mixed-theory discovery in the existing bounded fallback. *)
let linear premises conclusion =
  let needs_arithmetic = ref false in
  let arithmetic f = match Form.pform f with
    | Fatom a -> (match Atom.atom a with
      | Abop ((BO_Zlt | BO_Zle | BO_Zge | BO_Zgt),_,_) ->
        needs_arithmetic := true; true
      | Abop (BO_eq ty,a,b) when SmtBtype.HashedBtype.equal ty SmtBtype.TZ ->
        let interpreted a = match Atom.atom a with Aapp _ -> false | _ -> true in
        if interpreted a || interpreted b then needs_arithmetic := true;
        true
      | _ -> false)
    | Fapp ((Ftrue | Ffalse),_) -> true
    | _ -> false in
  let clause = List.sort_uniq (fun a b -> Int.compare (lit a) (lit b))
    (conclusion @ List.map Form.neg premises) in
  if List.length clause > 64 || not (List.for_all arithmetic clause) ||
     not !needs_arithmetic || List.map lit clause = [0] then None
  else Stdlib.Option.map (fun proof -> Linear proof) (Lia.build_lia_certif clause)

let select ~premises ~conclusion =
  if List.map lit conclusion=[0] then Some Truth else
  if List.exists (fun cs -> List.map lit cs=List.map lit conclusion) premises then Some Identity else
  match units premises with
  | None -> None
  | Some ps -> match conclusion with
    | [goal] when transitive goal ps -> Some Trans
    | [goal] -> (match congruent goal ps with
      | Some args -> Some (Congruence args)
      | None -> linear ps conclusion)
    | _ -> linear ps conclusion

(* Reuse an existing arithmetic candidate when its checked global clause is
   exactly the implication of the actual premises and conclusion. Resolution
   and temporary local clause arrays are then unnecessary in Rocq. *)
let from_witness ~premises ~conclusion w =
  match units premises with None -> None | Some ps ->
  let conditional=Certificate.canonical (conclusion @ List.map neg ps) in
  if conditional=[0] then None else
  List.find_map (fun cmd ->
    if cmd.Certificate.expected<>conditional then None else
    match cmd.Certificate.action with
    | Certificate.LiaMicromega(_,cl,proof) when cl=conditional -> Some(Linear proof)
    | _ -> None) w.Certificate.program
let to_coq ~constructor =
  let open RocqInterface in let open CoqTerms in
  let app c args=mkApp(c,Array.of_list args) in
  let list ty f xs=List.fold_right(fun x tail->app(Lazy.force ccons)[ty;f x;tail])xs(app(Lazy.force cnil)[ty])in
  function
  | Truth -> constructor "Truth"
  | Identity -> constructor "Identity"
  | Trans -> constructor "Trans"
  | Congruence args ->
    let ty=Lazy.force cint in let option_ty=app(Lazy.force coption)[ty]in
    let option=function None->app(Lazy.force cNone)[ty]|Some l->app(Lazy.force cSome)[ty;mkInt l]in
    app(constructor "Congruence")[list option_ty option args]
  | Linear proof -> app(constructor "Linear")
      [list(Lazy.force micromega_coq_proofTerm) micromega_dump_proof_term proof]

(* Optional whole-certificate arithmetic compression. A small syntactic budget
   bounds Boolean expansion; larger/mixed inputs retain the CVC5 translation. *)
let compress ~premises ~conclusion =
  match units premises with None -> None | Some ps ->
  let nodes = ref 0 and atoms = ref 0 and interpreted = ref false in
  let rec supported f =
    incr nodes;
    !nodes <= 64 && match Form.pform f with
    | Fatom a ->
      incr atoms;
      !atoms <= 12 && (match Atom.atom a with
      | Abop ((BO_Zlt | BO_Zle | BO_Zge | BO_Zgt),_,_) -> interpreted := true; true
      | Abop (BO_eq ty,a,b) when SmtBtype.HashedBtype.equal ty SmtBtype.TZ ->
        let ground a = match Atom.atom a with Aapp _ -> false | _ -> true in
        if ground a || ground b then interpreted := true;
        true
      | _ -> false)
    | Fapp ((Ftrue | Ffalse | Fand | For | Fimp | Fiff | Fxor | Fite | Fnot2 _),xs) ->
      Array.for_all supported xs
    | _ -> false in
  let conditional = List.sort_uniq (fun a b -> Int.compare (lit a) (lit b))
    (conclusion @ List.map Form.neg ps) in
  if not (List.for_all supported conditional) || not !interpreted then None else
    Stdlib.Option.map (fun proof -> Linear proof) (Lia.build_lia_certif conditional)
