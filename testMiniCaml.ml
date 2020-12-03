(* Test di MiniCaml (modulo importato) *)
open MiniCaml;;

let rec print_exp (a : exp) =
    let b = eval a global_envt in match b with
        | Int n -> print_int n; Printf.printf("\n")
        | Bool b -> if b then print_int 1 else print_int 0; Printf.printf("\n")
		| String s -> print_string s; Printf.printf("\n")
        | _ -> failwith("Ornitorinco")
;;

let a = Let("x", EInt(2), Let("y", EInt(3), Let("z", Sum(Den("x"), Den("y")), Letrec("fact", "n", IfThenElse(Eq(Den("n"), EInt(1)), EInt(1), Times(Den("n"), Apply(Den("fact"), Sub(Den("n"), EInt(1))))), Apply(Den("fact"), EInt (8))))))


(* Test per funzioni ricorsive (ok) *)
let a' = Let("x",EInt 6,Letrec("fact","n",IfThenElse(Eq(Den("n"), EInt 1), EInt 1, Times(Den("n"), Apply(Den("fact"), Sub(Den("n"), EInt 1)))),Apply(Den("fact"), Den "x")))

(* Test per scoping statico (ok) *)
let a'' = Let("n", EInt 5, Let("f", Fun("x", Sum(Den("x"), Den("n"))), Let("n", EInt 67, Apply(Den("f"), EInt 5))))

(* Test per stringhe *)
let a''' = Let("x", EString "pippo", Den("x"))
;;

print_exp a; print_exp a'; print_exp a'';; print_exp a''';;