(* Untrusted compilation: retain the dependency graph of the final conflict.
   The resulting semantic certificate is fully checked in Rocq, including all
   its remaining steps and scopes. This is not CPC conformance validation. *)
module E = EunoiaElaborate
let compile (proof:E.proof) =
  let steps = Hashtbl.create (List.length proof.steps) in
  List.iter (fun (st:E.step) -> Hashtbl.add steps st.id st) proof.steps;
  let needed = Hashtbl.create (List.length proof.steps) in
  let rec require id = if not (Hashtbl.mem needed id) then begin
    Hashtbl.add needed id ();
    match Hashtbl.find_opt steps id with
    | None -> ()
    | Some st -> List.iter require st.E.premises
  end in
  require proof.conflict;
  let keep (st:E.step) = Hashtbl.mem needed st.id in
  let rec trace = function
    | E.Done -> E.Done
    | E.Next (st,rest) -> if keep st then E.Next(st,trace rest) else trace rest
    | E.Push (slot,a,body,closing,rest) ->
      if keep closing then E.Push(slot,a,trace body,closing,trace rest)
      else trace rest in
  {proof with steps=List.filter keep proof.steps;trace=trace proof.trace}
