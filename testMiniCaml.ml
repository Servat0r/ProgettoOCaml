(* Test di MiniCaml (modulo importato) *)
open MiniCaml;;

(* Una println per visualizzare le espressioni ottenute come risultato *)
let rec println_evT (e : evT) =
    (* Stampa senza aggiungere un ritorno a capo*)
    let rec print_evT (e : evT) = match e with
    |Int n -> print_int n
    |Bool b -> if b then print_string "true" else print_string "false"
    |String s -> print_string s
    | _ -> failwith("Unacceptable value")
    (* Stampa in-line di una lista *)
    in let rec print_list l = match l with
        | [] -> ()
        | p::q -> print_evT p; print_string " "; print_list q
    in match e with
        | Int n -> print_evT e; Printf.printf("\n")
        | Bool b -> print_evT e; Printf.printf("\n")
		| String s -> print_evT e; Printf.printf("\n")
        | Set(t,l) -> if l = [] then print_string "Set: {}\n" else (print_string "Set: { "; print_list l; print_string "}\n")
        | _ -> failwith("Unprintable value")
;;

let env0=global_envt;;

(* Permette di stampare (sia da shell sia dopo compilazione) il risultato delle valutazione di un'espressione *)
let peval (e: exp) (s: evT env) = println_evT (eval e s);;

(* Stampa un messaggio di errore (da usare nei try-with in fondo) *)
let print_error () = print_string "RuntimeError\n"

(* Test per funzioni ricorsive *)
let a' = Let("x",EInt 6,Letrec("fact","n", IfThenElse(Eq(Den("n"), EInt 1), EInt 1, Times(Den("n"), Apply(Den("fact"), Sub(Den("n"), EInt 1)))),Apply(Den("fact"), Den "x")))

(* Test per scoping statico *)
let a'' = Let("n", EInt 5, Let("f", Fun("x", Sum(Den("x"), Den("n"))), Let("n", EInt 67, Apply(Den("f"), EInt 5))))

(* Test per stringhe *)
let a = Let("x", EString "pippo", Den("x"))

(* Test per interi *)
let b = Let("y", EInt 4, Den("y"))

(* Test per booleani *)
let c = Let("z", True, Den("z"))

(* Test per funzioni primitive aggiunte: pow , lessThan, greaterThan*)
let potenza=Pow(EInt 2,EInt 4)

let meno_di1=LessThan(EInt 2,EInt 4)

let meno_di2=LessThan(EInt 4,EInt 2)

let piu_di1=GreaterThan(EInt 4,EInt 2)

let piu_di2=GreaterThan(EInt 2,EInt 4)


;;

(* TESTS PER INSIEMI *)

let insieme_vuoto = Empty(TInt)

let insieme_1_elem = Singleton(TInt,EInt 4)

let insieme = Of(TInt,[EInt 4;EInt 8])

let verifica_vuoto1 = IsEmpty(insieme_vuoto)

let verifica_vuoto2 = IsEmpty(insieme_1_elem)

let contiene_x = Contains (insieme,EInt 4)

let non_contiene_x = Contains (insieme,EInt 100)

let sottoinsieme= IsSubset(insieme_1_elem,insieme)

let non_sottoinsieme= IsSubset(insieme_1_elem,Of(TInt,[EInt 200;EInt 300;EInt 400]))

let insert=Insert(insieme,EInt 300)

let rimozione=Remove(insert,EInt 300)

let min=GetMin(insieme)

let max=GetMax(insieme)

let tuttimaggiori1=For_all(Fun("x", GreaterThan(Den "x", EInt 0)),insieme)

let tuttimaggiori2=For_all(Fun("x", GreaterThan(Den "x", EInt 0)),insieme_1_elem)

let unomaggiore1=Exists(Fun("x",GreaterThan(Den "x", EInt 1)),insieme)

let unomaggiore2=Exists(Fun("x",GreaterThan(Den "x", EInt 1)),insieme_1_elem)

let lista_minori=Filter(Fun("x",LessThan(Den "x",EInt 5)), insieme)

let lista_maggiori=Filter(Fun("x",GreaterThan(Den "x", EInt 3)),insieme)

let prova_map=Let("f", Fun("x", IfThenElse(Eq(Den "x", EInt 0), EString "p", EString "q")), Let("s", Of(TInt, [EInt 0; EInt 54; EInt 8]), Map(Den "f", Den "s")))

let prova_unione = Union(Of(TInt, [EInt 6; EInt 8; EInt 3; EInt 45; EInt 12]),Of(TInt, [EInt 5; EInt 8; EInt 3; EInt 89]))

let prova_intersezione = Intersection(Of(TInt, [EInt 6; EInt 8; EInt 3; EInt 45; EInt 12]),Of(TInt, [EInt 5; EInt 8; EInt 3; EInt 89]))

let prova_differenza = Difference(Of(TInt, [EInt 6; EInt 8; EInt 3; EInt 45; EInt 12]),Of(TInt, [EInt 5; EInt 8; EInt 3; EInt 89]))

(* Errori *)
let errore_set_1_elem=Singleton(TInt,EString "aiutooo") 

let errore_set_tipi_diversi=Of(TInt,[EString "erorre"; EInt 8]) 

let errore_controllo_contenimento=Contains(insieme,EString "nope") 

let errore_contenimento_insiemi=IsSubset(insieme_1_elem,Singleton(TString,EString "nope")) 

let errore_inserimento=Insert(insieme,EString "sbalgiato")

let errore_rimozione=Remove(insieme,EInt 150)

;;


(*Stampa per funzioni ricorsive*)
Printf.printf "\n\n****Funzione ricorsive****\n";;
peval a' env0;;

(*Stampa per scoping statico*)
Printf.printf "\n\n****Scoping statico****\n";;
peval a'' env0;;

(*Stampa per variabili dell'ambiente*)
Printf.printf "\n\n****Variabili ambiente****\n";;
peval a env0;;
peval b env0;;
peval c env0;;


(*Stampa funzioni primitive: pow , LessThan, GreaterThan*)
Printf.printf "\n\n****Funzioni primitive aggiunte****\n";;
peval potenza env0;;
peval meno_di1 env0;;
peval meno_di2 env0;;
peval piu_di1 env0;;
peval piu_di2 env0;;


(*Stampa per Insiemi*)
Printf.printf "\n\n****Insiemi****\n";;
peval insieme_vuoto env0;;
peval insieme_1_elem env0;;
peval insieme env0;;


(*Stampa per unione, intersezione e differenza*)
Printf.printf "\n\n****Unione, Intersezione e Differenza fra insiemi****\n";;
peval prova_unione env0;;
peval prova_intersezione env0;;
peval prova_differenza env0;;


(*Stampa per operatori unari su insiemi*)
Printf.printf "\n\n****Operatori unari insiemi****\n";;
peval verifica_vuoto1 env0;;
peval verifica_vuoto2 env0;;
peval min env0;;
peval max env0;;


(*Stampa per operatori binari su insiemi*)
Printf.printf "\n\n****Operatori binari insiemi****\n";;
peval contiene_x env0;;
peval non_contiene_x env0;;
peval sottoinsieme env0;;
peval non_sottoinsieme env0;;
peval insert env0;;
peval rimozione env0;;


(*Stampa per operatori funzionali su insiemi*)
Printf.printf "\n\n****Operatori funzionali insiemi****\n";;
peval tuttimaggiori1 env0;;
peval tuttimaggiori2 env0;;
peval unomaggiore1 env0;;
peval unomaggiore2 env0;;
peval lista_minori env0;;
peval lista_maggiori env0;;
peval prova_map env0;;


(*Errori*)
Printf.printf "\n\n****Errori****\n";;
try peval errore_set_1_elem env0 with RuntimeError -> print_error();;
try peval errore_set_tipi_diversi env0 with RuntimeError  -> print_error();;
try peval errore_controllo_contenimento env0 with RuntimeError -> print_error();;
try peval errore_contenimento_insiemi env0 with RuntimeError -> print_error();;
try peval errore_inserimento env0 with RuntimeError -> print_error();;
try peval errore_rimozione env0 with RuntimeError -> print_error();;