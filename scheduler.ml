
exception Combinational_cycle
open Netlist_ast

let rec (++) l1 l2 =
  match l1 with
      [] -> l2
    | x :: xs -> xs ++ (if List.mem x l2 then l2 else x :: l2)

let arg_idents = function
  | Avar ident -> [ident]
  | Aconst _ -> []

let expr_idents_depends = function
    | Earg arg -> arg_idents arg
    | Ereg ident -> []
    | Enot arg -> arg_idents arg
    | Ebinop(_, arg1, arg2) -> (arg_idents arg1) ++ (arg_idents arg2)
    | Emux(arg1, arg2, arg3) -> (arg_idents arg1) ++ (arg_idents arg2) ++ (arg_idents arg3)
    | Erom(_, _, read_addr) -> (arg_idents read_addr)
    | Eram(_, _, read_addr, write_enable, write_addr, data) -> (arg_idents read_addr)
    | Econcat(arg1, arg2) -> (arg_idents arg1) ++ (arg_idents arg2)
    | Eslice(_, _, arg) -> arg_idents arg
    | Eselect(_, arg) -> arg_idents arg

let expr_idents_rev_depends = function
    | Earg arg -> []
    | Ereg ident -> [ident]
    | Enot arg -> []
    | Ebinop(_, arg1, arg2) -> []
    | Emux(arg1, arg2, arg3) -> []
    | Erom(_, _, read_addr) -> []
    | Eram(_, _, read_addr, write_enable, write_addr, data) -> (arg_idents write_enable) ++ (arg_idents write_addr) ++ (arg_idents data)
    | Econcat(arg1, arg2) -> []
    | Eslice(_, _, arg) -> []
    | Eselect(_, arg) -> []

let read_exp (value, expr) = expr_idents_depends expr

let depends eq1 eq2 =
  List.mem (fst eq1) (read_exp eq2)

let print_eq_idents (x, _) =
  print_string x
let print_ee (eq1, eq2) =
  print_eq_idents eq1; print_string ", ";
  print_eq_idents eq2
		   
let schedule p =
  let open Graph in
do_print := Obj.magic print_eq_idents;
  let h = Hashtbl.create 17 in
  let g = mk_graph () in
  List.iter (fun eq -> 
	let n = { n_label = eq; n_mark = NotVisited; n_link_to = []; n_linked_by = [] } in
	Hashtbl.add h (fst eq) n;
    g.g_nodes <- n :: g.g_nodes) p.p_eqs;
  let ae id1 id2 =
	try
	  let n1 = Hashtbl.find h id1 in
	  let n2 = Hashtbl.find h id2 in
	  n1.n_link_to <- n2 :: n1.n_link_to;
	  n2.n_linked_by <- n1 :: n2.n_linked_by
	with Not_found -> ()
  in
  List.iter (fun eq1 ->
	List.iter (fun id2 -> ae id2 (fst eq1)) (expr_idents_depends (snd eq1))
  ) p.p_eqs;
  List.iter (fun eq1 ->
	List.iter (ae (fst eq1)) (expr_idents_rev_depends (snd eq1))
  ) p.p_eqs;
  try
    {p with p_eqs = Graph.topological g}
  with
      Graph.Cycle -> raise Combinational_cycle

