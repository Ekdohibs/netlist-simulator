exception Cycle
type mark = NotVisited | InProgress | Visited

type 'a graph =
    { mutable g_nodes : 'a node list }
and 'a node = {
  n_label : 'a;
  mutable n_mark : mark;
  mutable n_link_to : 'a node list;
  mutable n_linked_by : 'a node list;
}

let mk_graph () = { g_nodes = [] }

let add_node g x =
  let n = { n_label = x; n_mark = NotVisited; n_link_to = []; n_linked_by = [] } in
  g.g_nodes <- n::g.g_nodes

let node_for_label g x =
  List.find (fun n -> n.n_label = x) g.g_nodes

let add_edge g id1 id2 =
  let n1 = node_for_label g id1 in
  let n2 = node_for_label g id2 in
  n1.n_link_to <- n2::n1.n_link_to;
  n2.n_linked_by <- n1::n2.n_linked_by

let clear_marks g =
  List.iter (fun n -> n.n_mark <- NotVisited) g.g_nodes

let find_roots g =
  List.filter (fun n -> n.n_linked_by = []) g.g_nodes

let do_print = ref ()
			  
let rec dfs g n r =
  if n.n_mark = InProgress then
    (List.iter (fun n -> if n.n_mark = InProgress then
				((Obj.magic !do_print) n.n_label; print_newline ())) g.g_nodes;
	  raise Cycle)
  else if n.n_mark = Visited then
    r
  else begin
    n.n_mark <- InProgress;
    let rr = List.fold_left (fun rr nn -> dfs g nn rr) r n.n_link_to in
    n.n_mark <- Visited;
    n :: rr
  end

let has_cycle g =
  clear_marks g;
  try
    List.iter (fun n -> ignore (dfs g n [])) g.g_nodes;
    false
  with
      Cycle -> true
       
let topological g =
  clear_marks g;
  List.map (fun n -> n.n_label)
    (List.fold_left (fun rr nn -> dfs g nn rr) [] g.g_nodes)

