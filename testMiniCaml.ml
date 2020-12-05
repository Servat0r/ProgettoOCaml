(* Test di MiniCaml (modulo importato) *)
open MiniCaml;;

(* Aggiustare dopo per non stampare su righe diverse tutti gli elementi di un insieme *)
let rec print_evT (e : evT) (b : bool)=
    let rec print_list l = match l with
        | [] -> ()
        | p::q -> print_evT p false; print_string " "; print_list q
    in match e with
        | Int n -> print_int n; if b then Printf.printf("\n") else ()
        | Bool d -> if d then print_string "true" else print_string "false"; if b then Printf.printf("\n") else ()
		| String s -> print_string s; if b then Printf.printf("\n") else ()
        | Set(t,l) -> print_string "Insieme di: "; print_list l
        | _ -> failwith("Ornitorinco")
;;

(* OPERATORI: I seguenti operatori sono qui ridefiniti per permettere una scrittura più agevole delle espressioni di 
let ( +: )
let ( -: )
let ( *: )
let ( **: )
let ( &: )
let ( |: )
let ( !: )
let makeEmpty
let makeSingle
let makeOf
let insertIn
let removeFrom
let 
*)

let a = Let("x", EInt(2), Let("y", EInt(3), Let("z", Sum(Den("x"), Den("y")), Letrec("fact", "n", TInt, TInt, IfThenElse(Eq(Den("n"), EInt(1)), EInt(1), Times(Den("n"), Apply(Den("fact"), Sub(Den("n"), EInt(1))))), Apply(Den("fact"), EInt (8))))))


(* Test per funzioni ricorsive (ok) *)
let a' = Let("x",EInt 6,Letrec("fact","n",TInt, TInt, IfThenElse(Eq(Den("n"), EInt 1), EInt 1, Times(Den("n"), Apply(Den("fact"), Sub(Den("n"), EInt 1)))),Apply(Den("fact"), Den "x")))

(* Test per scoping statico (ok) *)
let a'' = Let("n", EInt 5, Let("f", Fun("x", TInt, TInt, Sum(Den("x"), Den("n"))), Let("n", EInt 67, Apply(Den("f"), EInt 5))))

(* Test per stringhe *)
let a''' = Let("x", EString "pippo", Den("x"))

(* Tests per insiemi *)
let a'''' = Let("s", Of(TInt, [EInt 56; EInt 78; EInt 2]), Let("t",Of(TInt, [EInt 56; EInt 2]), IsSubset(Den("t"), Den("s"))))

(* let v = Let("a",Of(TSet(TInt), []),Insert(Den("a"), Den("a"))) *)


let v = Let("a", Of(TString, [EString "we"; EString "p"; EString "alalalalalalala"]), GetMax(Den("a")))


(* let w = Let("s", Of(TInt, [True]), Den("s")) *)

;;

(* Qui va però; boh 
print_evT (set_getMax (Set(TInt,[Int 5; Int 8; Int 3]))) true;; *)

print_evT (eval a global_envt) true; print_evT (eval a' global_envt) true; print_evT (eval a'' global_envt) true; 
print_evT (eval a''' global_envt) true; print_evT (eval a'''' global_envt) true;
print_evT (eval v global_envt) true; (* print_evT (eval w global_envt) *);;