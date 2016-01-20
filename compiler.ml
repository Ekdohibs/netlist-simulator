open Netlist_ast

let print_only = ref false
let io_mode = ref 0
let number_steps = ref (-1)

type location = {
  varname : string;
  start_pos : int;
  length : int;
  n_copies : int;
  is_computed : bool
}

let ident_length p ident =
  try
    let t = Env.find ident p.p_vars in
    match t with
      | TBit -> 1
      | TBitArray n -> n
  with
      Not_found -> failwith ("arg not found: " ^ ident)

let shift_left arg amount =
  if amount = 0 then arg else "((" ^ arg ^ ")<<" ^ (string_of_int amount) ^ ")"

let shift_right arg amount =
  assert (amount >= 0);
  if amount = 0 then arg else "((" ^ arg ^ ")>>" ^ (string_of_int amount) ^ ")"
 

let arg_length p = function
  | Avar id -> ident_length p id
  | Aconst (VBit _) -> 1
  | Aconst (VBitArray ba) -> Array.length ba

let sl x shift_amount =
  assert (shift_amount >= 0);
  if shift_amount >= 64 then 0L
  else Int64.shift_left x shift_amount
										  
let mask a b =
  Int64.(to_string (sub (sl one b) (sl one a)))

let compile_arg locations need_clean = function
  | Avar id -> let a = Hashtbl.find locations id in
			   if a.n_copies = 0 then "0" else
				 let shifted = shift_right a.varname a.start_pos in
				 if a.n_copies > 1 then
				   if need_clean then
					 "((-(" ^ shifted ^ "&1" ^ "))&" ^ (mask 0 a.n_copies) ^ ")"
				   else
					 "(-(" ^ shifted ^ "&1))"
				 else
				   if need_clean then
					 "(" ^ shifted ^ "&" ^ (mask 0 a.length) ^ ")"
				   else shifted
  | Aconst (VBit b) -> if b then "1" else "0"
  | Aconst (VBitArray ba) -> Int64.(to_string (
    Array.fold_left (fun a b -> logor (sl a 1) (if b then one else zero)) zero ba
  ))

let compile_arg_shifted locations need_clean shift id = 
  let a = Hashtbl.find locations id in
	  if a.n_copies = 0 then "0" else
		let shifted = shift_right a.varname shift in
		let fpos = a.start_pos - shift in
		if a.n_copies > 1 then
		  if need_clean then
			"((-(" ^ shifted ^ "&" ^ (mask fpos (fpos + 1)) ^ "))&" ^ (mask fpos (fpos + a.n_copies)) ^ ")"
		  else
			"(-(" ^ shifted ^ "&" ^ (mask fpos (fpos + 1)) ^ "))"
		else
		  if need_clean then
			"(" ^ shifted ^ "&" ^ (mask fpos (fpos + a.length)) ^ ")"
		  else shifted
								
let compile_eq p memories locations (ident, expr) =
  let a = Hashtbl.find locations ident in
  if a.is_computed then "" else
  let ca = compile_arg locations in
  let cas = compile_arg_shifted locations in
  match expr with
      Ereg _ -> ""
    | _ ->
  ident ^ " = " ^ 
  (match expr with
    | Earg arg -> ca false arg
	| Enot (Avar id) -> "~" ^ (let a = Hashtbl.find locations id in a.varname)
    | Enot arg -> "~" ^ (ca false arg)
    | Ebinop(binop, Avar id1, Avar id2) ->
	  let a = Hashtbl.find locations id1 in
	  let b = Hashtbl.find locations id2 in
	  let off = a.start_pos - b.start_pos in
        (if binop = Nand then "~(" else "(") ^
		(cas false (max off 0) id1) ^
		(match binop with Or -> "|" | Xor -> "^" | _ -> "&") ^
		(cas false (max (-off) 0) id2) ^
		")"
    | Ebinop(binop, arg1, arg2) ->
        (if binop = Nand then "~(" else "(") ^
		(ca false arg1) ^
		(match binop with Or -> "|" | Xor -> "^" | _ -> "&") ^
		(ca false arg2) ^
		")"
	| Emux(Avar id1, Avar id2, Avar id3) ->
	  let a = Hashtbl.find locations id1 in
	  let b = Hashtbl.find locations id2 in
	  let c = Hashtbl.find locations id3 in
	  let ns = min (min a.start_pos b.start_pos) c.start_pos in
	  let ac = cas false (a.start_pos - ns) id1 in
	  let bc = cas false (b.start_pos - ns) id2 in
	  let cc = cas false (c.start_pos - ns) id3 in
	  (* "(" ^ ac ^ "&(~" ^ cc ^ "))|(" ^ bc ^ "&" ^ ")" *)
	  ac ^ "^((" ^ ac ^ "^" ^ bc ^ ")&" ^ cc ^")"
    | Emux(arg1, arg2, arg3) ->
	  let ac = ca false arg1 in
	  let bc = ca false arg2 in
	  let cc = ca false arg3 in
	  (* "(" ^ ac ^ "&(~" ^ cc ^ "))|(" ^ bc ^ "&" ^ cc ^ ")" *)
	  ac ^ "^((" ^ ac ^ "^" ^ bc ^ ")&" ^ cc ^")"
    | Eselect(i, arg) -> (shift_right (ca false arg) ((arg_length p arg) - i - 1)) ^ "&1"
    | Eslice(i, j, arg) -> (shift_right (ca false arg) ((arg_length p arg) - j - 1)) ^ "&" ^ (mask 0 (j - i + 1))
    | Econcat(arg1, arg2) -> (shift_left (ca false arg1) (arg_length p arg2)) ^ "|" ^ (ca true arg2)
    | Eram(addr_size, word_size, read_addr, write_enable, write_addr, data) -> (Hashtbl.find memories ident) ^ "[" ^ (ca true read_addr) ^ "]"
    | Erom(addr_size, word_size, read_addr) -> (Hashtbl.find memories ident) ^ "[" ^ (ca true read_addr) ^ "]"
	| _ -> assert false
  ) ^ ";\n"

let compile_eq2 p memories locations (ident, expr) =
  let ca = compile_arg locations in
  match expr with
    (* | Ereg id -> ident ^ " = " ^ (ca false (Avar id)) ^ ";\n" *)
    | Ereg id -> ident ^ " = " ^ id ^ ";\n" 
    | Eram(addr_size, word_size, read_addr, write_enable, write_addr, data) -> (Hashtbl.find memories ident) ^ "[" ^ (ca true write_addr) ^ "]^=((-" ^ (ca true write_enable) ^ ")&(" ^ (ca true data) ^ "^" ^ (Hashtbl.find memories ident) ^ "[" ^ (ca true write_addr) ^ "]));\n"
    | _ -> ""

type oeq =
| Onot of string
| Oreg of string
| Obinop of binop * string * string * int
| Omux of string * string * string * int * int

let compute_locations p memories locations =
  Env.iter (fun arg _ -> Hashtbl.add locations 
	arg { varname = arg; start_pos = 0; length = ident_length p arg; is_computed = false; n_copies = 1 }
  ) p.p_vars;
  let comp = Hashtbl.create 17 in
  List.iter (fun (ident, expr) ->
	match expr with
	| Earg (Avar arg) -> Hashtbl.replace locations ident (Hashtbl.find locations arg)
	| Eselect(i, Avar arg) ->
	  let a = Hashtbl.find locations arg in
	  Hashtbl.replace locations ident
	   (if a.n_copies = 1 then
		  (assert (0 <= i && i <= a.length - 1);
		  { varname = a.varname; start_pos = a.start_pos + a.length - i - 1;
			length = 1; is_computed = true; n_copies = 1 })
		else
		  { varname = a.varname; start_pos = a.start_pos;
			length = 1; is_computed = true; n_copies = 1 })
	| Eslice(i, j, Avar arg) ->
	  let a = Hashtbl.find locations arg in
	  Hashtbl.replace locations ident
		(if a.n_copies = 1 then
		  (assert (0 <= i && i <= j && j <= a.length - 1);
		  { varname = a.varname; start_pos = a.start_pos + a.length - j - 1;
			length = j - i + 1; is_computed = true; n_copies = 1 })
		else
		  { varname = a.varname; start_pos = a.start_pos;
			length = 1; is_computed = true; n_copies = j - i + 1 })
	| Econcat(Avar arg1, Avar arg2) ->
	  let a = Hashtbl.find locations arg1 in
	  let b = Hashtbl.find locations arg2 in
	  if a.varname = b.varname && b.start_pos + b.length = a.start_pos && a.n_copies = 1 && b.n_copies = 1 then
		Hashtbl.replace locations ident
		  { varname = a.varname; start_pos = b.start_pos;
			length = a.length + b.length; is_computed = true; n_copies = 1 }
	  else if a.varname = b.varname && a.start_pos = b.start_pos && a.length = 1 && b.length = 1 then
		Hashtbl.replace locations ident
		  { varname = a.varname; start_pos = a.start_pos;
			length = 1; is_computed = true; n_copies = a.n_copies + b.n_copies }
	| Enot(Avar arg) ->
	  let a = Hashtbl.find locations arg in
	  Hashtbl.replace locations ident (begin
	  try
		let b = Hashtbl.find comp (Onot a.varname) in
		{ varname = b.varname; start_pos = a.start_pos;
		  length = a.length; is_computed = true; n_copies = a.n_copies }
	  with
		Not_found -> let b = { varname = ident; start_pos = a.start_pos;
							   length = a.length; is_computed = false; n_copies = a.n_copies }
					 in Hashtbl.add comp (Onot a.varname) b; b
	  end)
	| Ereg arg ->
	  let a = Hashtbl.find locations arg in
	  Hashtbl.replace locations ident (begin
	  try
		let b = Hashtbl.find comp (Oreg a.varname) in
		{ varname = b.varname; start_pos = a.start_pos;
		  length = a.length; is_computed = true; n_copies = 1 }
	  with
		Not_found -> let b = { varname = ident; start_pos = a.start_pos;
							   length = a.length; is_computed = false; n_copies = a.n_copies }
					 in Hashtbl.add comp (Oreg a.varname) b; b
	  end)
	| Ebinop(binop, Avar arg1, Avar arg2) ->
	  let a = Hashtbl.find locations arg1 in
	  let b = Hashtbl.find locations arg2 in
	  if a.n_copies = 1 && b.n_copies = 1 then
		let key = Obinop(binop, a.varname, b.varname, a.start_pos - b.start_pos) in
		Hashtbl.replace locations ident (begin
		  try
		    let c = Hashtbl.find comp key in
		    { varname = c.varname; start_pos = min a.start_pos b.start_pos;
			  length = a.length; is_computed = true; n_copies = 1 }
		  with
		    Not_found ->
			  let c = { varname = ident; start_pos = min a.start_pos b.start_pos;
			  		  length = a.length; is_computed = false; n_copies = 1 }
			  in Hashtbl.add comp key c; c
	    end)
	| Emux(Avar arg1, Avar arg2, Avar arg3) ->
	  let a = Hashtbl.find locations arg1 in
	  let b = Hashtbl.find locations arg2 in
	  let c = Hashtbl.find locations arg3 in
	  if a.n_copies = 1 && b.n_copies = 1 && c.n_copies = 1 then
  	    let key = Omux(a.varname, b.varname, c.varname,
  		  			 c.start_pos - a.start_pos, c.start_pos - b.start_pos) in
  	    Hashtbl.replace locations ident (begin
		  try
		    let d = Hashtbl.find comp key in
		    { varname = d.varname;
			  start_pos = min (min a.start_pos b.start_pos) c.start_pos;
			  length = a.length;
			  is_computed = true;
			  n_copies = 1
			}
		  with
			Not_found ->
			  let d = { varname = ident;
						start_pos = min (min a.start_pos b.start_pos) c.start_pos;
						length = a.length;
						is_computed = false;
						n_copies = 1
					  }
			  in Hashtbl.add comp key d; d
	    end)
	| _ -> ()
  ) p.p_eqs
	

let header =
"#include <stdio.h>
#include <stdlib.h>

void __read_file(char* filename, int addr_size, int word_size, unsigned long long int* array) {
    FILE* fp;
    fp = fopen(filename, \"r\");
    if (fp == NULL) {
        perror(\"Error while opening ROM\\n\");
        exit(1);
    }
    int num_chars = ((1 << addr_size) * word_size + 7) / 8;
    unsigned long long int current = 0;
    int num_read_bits = 0;
    int read_index = 0;
    for (int i = 0; i < num_chars; i++) {
        current = (current << 8) | fgetc(fp);
        num_read_bits += 8;
        while (num_read_bits >= word_size) {
            unsigned long long int mask = (num_read_bits == 64) ? 0 : (1 << num_read_bits);
            num_read_bits -= word_size;
            mask -= 1 << num_read_bits;
            array[read_index] = (current & mask) >> num_read_bits;
            read_index++;
        }
    }
}

int __rom_id = 1;
int main(int __argc, char** __argv) {

"

let read_inputs p locations ff =
  match !io_mode with
  | 0 -> List.iter (fun id -> Format.fprintf ff
	"printf(\"%s = ?\\n\"); scanf(\"%%llu\", &%s);\n" id id) p.p_inputs
  | 1 -> List.iter (fun id ->
	let size = ident_length p id in
	Format.fprintf ff "%s = 0;\n" id;
	for i = 0 to size - 1 do
	  Format.fprintf ff "%s = (%s << 1) | (getchar() & 1);\n" id id
	done;
     ) p.p_inputs
  | 2 -> List.iter (fun id ->
	let size = ident_length p id in
	let k = (size - 1) / 8 in
	Format.fprintf ff "%s = getchar();\n" id;
	for i = 0 to k - 1 do
	  Format.fprintf ff "%s = (%s << 8) | getchar();\n" id id
	done;
     ) p.p_inputs
  | _ -> failwith "invalid io mode"

let print_outputs p locations ff =
  match !io_mode with
  | 0 -> List.iter (fun id -> Format.fprintf ff
	"printf(\"%s = %%llu\\n\", %s);\n" id (compile_arg locations true (Avar id))) p.p_outputs
  | 1 -> List.iter (fun id -> 
	let size = ident_length p id in
	let a = Hashtbl.find locations id in
	for i = 0 to size - 1 do
	  Format.fprintf ff "putchar('0' | ((%s >> %d) & 1));\n" a.varname (a.start_pos + a.length - i - 1);
	done;
    ) p.p_outputs
  | 2 -> List.iter (fun id -> 
	let size = ident_length p id in
	let k = (size - 1) / 8 in
	for i = k downto 0 do
	  Format.fprintf ff "putchar((%s >> %d) & 255);\n" (compile_arg locations (i = k) (Avar id)) (8 * i);
	done;
    ) p.p_outputs
  | _ -> failwith "invalid io mode"

let compile filename =
  try
    let p = Netlist.read_file filename in
    let out_name = (Filename.chop_suffix filename ".net") ^ ".c" in
    let out_exe_name = Filename.chop_suffix filename ".net" in
    let out = open_out out_name in
    let close_all () =
      close_out out
    in
    let ff = Format.formatter_of_out_channel out in
    let p = Scheduler.schedule p in
    Format.fprintf ff "%s" header;
    Env.iter (fun id _ -> Format.fprintf ff "unsigned long long int %s = 0;\n" id) p.p_vars;
    let memories = Hashtbl.create 17 in
    let locations = Hashtbl.create 17 in
    List.iter (fun (ident, expr) -> match expr with
	| Eram(addr_size, word_size, read_addr, write_enable, write_addr, data) ->	   
	  Hashtbl.add memories ident ("__ram_" ^ ident);
	  Format.fprintf ff "unsigned long long int %s[%d] = {0};\n" ("__ram_" ^ ident) (1 lsl addr_size)
	| Erom(addr_size, word_size, read_addr) ->
	  Hashtbl.add memories ident ("__rom_" ^ ident);
	  Format.fprintf ff "unsigned long long int %s[%d];\n" ("__rom_" ^ ident) (1 lsl addr_size);
	  Format.fprintf ff "__read_file(__argv[__rom_id++], %d, %d, %s);\n" addr_size word_size ("__rom_" ^ ident)
    | _ -> ()
	) p.p_eqs;
    if (!number_steps = -1) then
      Format.fprintf ff "%s" "while (1) {\n"
    else
      Format.fprintf ff "for (int __loop_count = 0; __loop_count < %d; __loop_count++) {\n" !number_steps
    ;
	compute_locations p memories locations;
    read_inputs p locations ff;
    List.iter (fun eq -> Format.fprintf ff "%s" (compile_eq p memories locations eq)) p.p_eqs;
    print_outputs p locations ff;
    List.iter (fun eq -> Format.fprintf ff "%s" (compile_eq2 p memories locations eq)) p.p_eqs;
    Format.fprintf ff "%s" "}\nreturn 0;\n}\n";
    Format.fprintf ff "@.";
    close_all ();
    if not !print_only then
      let command = "gcc -std=c99 -O2 " ^ out_name ^ " -o " ^ out_exe_name in
      ignore (Unix.system command)
  with
    | Netlist.Parse_error s -> Format.eprintf "An error accurred: %s@." s; exit 2

let main () =
  Arg.parse
    ["-print", Arg.Set print_only, "Only print the C program";
     "-iomode", Arg.Set_int io_mode, "IO mode: 0 = inteactive, 1 = 0/1 (1 bit per char), 2 = binary (8 bits per char)";
     "-n", Arg.Set_int number_steps, "Number of steps to simulate"]
    compile
    ""
;;

main ()
