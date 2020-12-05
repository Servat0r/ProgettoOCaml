(* Interprete di MiniCaml esteso per il progetto di PR2 *)

(* TIPI DEFINITI *)

(* Identificatori *)
type ide = string;;

(* "Nomi" dei tipi di dato presenti per migliorare la leggibilità, anziché usare degli string literals come "int", "bool" etc *)
type tname = TInt | TBool | TString | TClosure | TRecClosure | TSet of tname | TUnBound

(* Abstract Expressions = espressioni nella sintassi astratta, compongono l'Albero di Sintassi Astratta *)
type exp = EInt of int
		| True 
		| False
		| EString of string
		| Den of ide
		(* Operatori binari da interi a interi*)
		| Sum of exp * exp
		| Sub of exp * exp
		| Times of exp * exp
		| Pow of exp * exp 
		(* Operatori da interi a booleani *)
		| IsZero of exp
		| Eq of exp * exp
		| LessThan of exp*exp
		| GreaterThan of exp*exp
		(* Operatori su booleani *)
		| And of exp*exp
		| Or of exp*exp
		| Not of exp
		(* Controllo del flusso, assegnamenti, funzioni *)
		| IfThenElse of exp * exp * exp
		| Let of ide * exp * exp
		| Letrec of ide * ide * exp * exp
		| Fun of ide * exp
		| Apply of exp * exp
		(* Costruttori di insiemi *)
		| Empty of tname (* Insieme vuoto *)
		| Singleton of tname*exp (* Insieme con un solo elemento *)
		| Of of tname*(exp list) (* Insieme con uno o più elementi *)
		(* Operatori unari su insiemi*)
		| IsEmpty of exp (* Insieme vuoto? *)
		| GetMin of exp (* Minimo elemento di un insieme; ma vale solo per gli interi? *)
		| GetMax of exp (* Massimo elemento di un insieme; ma vale solo per gli interi? *)
		(* Operatori binari su insiemi *)
		| Insert of exp*exp
		| Remove of exp*exp
		| Contains of exp*exp
		| IsSubset of exp*exp
		(* Operatori funzionali su insiemi *)
		| For_all of exp*exp (* controlla se tutti gli elementi dell’insieme soddisfano la proprietà definita dal parametro “predicate” *)
		| Exists of exp*exp (* controlla se esiste almeno un elemento dell’insieme che soddisfa la proprietà definita dal parametro “predicate” *)
		| Filter of exp*exp (* restituisce l’insieme degli elementi dell’insieme che soddisfano la proprietà definita dal parametro “predicate” *)
		| Map of exp*exp (* restitusce l’insieme dei valori v tali che v = function(x) dove x appartiene a aSet *)

(* Ambiente polimorfo; avremo un solo ambiente (globale), eventualmente copiato e passato ad altre funzioni *)
type 't env = string -> 't

(* Evaluation types = tipi primitivi esprimibili; le chiusure sono ricorsive di default *)
type evT = Int of int | Bool of bool | String of string | Closure of ide * exp * evT env | RecClosure of ide * ide * exp * evT env 
| Set of tname*(evT list) | UnBound

(* Da utilizzare per operazioni o funzioni applicate a oggetti di tipo non corretto *)
exception TypeError
(* Da utilizzare per valori passati a operazioni o funzioni di tipo corretto ma con valori "non corretti" *)
exception ValueError

(* Una mappa da evT a tname che a ogni valore col suo descrittore di tipo associa il nome del tipo *)
let (getType : evT -> tname) = function x -> match x with
	| Int(n) -> TInt
	| Bool(b) -> TBool
	| String(s) -> TString
	| Closure(i,e,en) -> TClosure
	| RecClosure(i,j,e,en) -> TRecClosure
	| Set(t,l) -> TSet(t)
	| UnBound -> TUnBound

(*
Per l'ambiente ne usiamo solo uno, per facilitare la creazione delle chiusure; di conseguenza, dovremo ricordarci dei nomi dei parametri
attuali di una funzione per ripristinare eventuali valori globali nel momento in cui si cancella un riferimento locale 
*)

(* Ambiente vuoto; non dovrà essere accessibile *)
let emptyenv = function x -> UnBound

(* Inizializzazione dell'ambiente globale come vuoto*)
let global_envt = emptyenv

(* Type-checking; non dovrà essere accessibile *)
let typecheck (x, y) = match x with	
        | TInt -> 
            	(match y with 
                        | Int(u) -> true
                        | _ -> false
						)
        | TBool -> 
            	(match y with 
                        | Bool(u) -> true
                        | _ -> false
						)
		| TString ->
				(match y with
					| String(u) -> true
					| _ -> false
				)
		| TSet(tn) ->
				(match y with
					(* Sicuro che vada bene così però? *)
					| Set(t, l) -> (if (tn = t) then let rec sameType (t : tname) (l : evT list) = match l with
														| [] -> true
														| p::q -> let t' = getType p in (if (t = t') then sameType t q else false)
						in sameType t l else false)
					| _ -> false
				)
        | TClosure -> 
				(match y with
					| Closure(i,e,n) -> true
					| _ -> false
				)
		| TRecClosure -> 
				(match y with
					| RecClosure(i,j,e,n) -> true
					| _ -> false
				)
		|TUnBound -> 
				(match y with
					| UnBound -> true
					| _ -> false
				)

(* Binding fra una stringa x e un valore primitivo evT; può essere usato per binding globali e locali, ovvero per lui NON è possibile
distinguere se lo si sta utilizzando in un assegnamento locale (Let o Letrec) o in uno globale (Bind): in quest'ultimo cqso i controlli
necessari (ad esempio per una funzione ricorsiva globale) li fa lui *)
let bind (s: evT env) (x: string) (v: evT) = function (i: string) -> if (i = x) then v else (s i)



(* UTILITIES per le primitive del linguaggio (NON sono primitive!) *)

(* Potenza di un intero; non dovrà essere accessibile *)
let rec pow x n = if n = 0 then 1 else x * (pow x (n-1))

(* Controlla se una lista contiene o meno un elemento *)
let rec list_contains l x = match l with
	| [] -> false
	| p::q -> if x = p then true else list_contains q x

(* Controlla che una lista non abbia elementi ripetuti *)
let rec checkNotEquals l = match l with
	| [] -> true
	| p::q -> if (not(list_contains q p)) then checkNotEquals q else false 

(* Requires: l1 ed l2 non hanno elementi ripetuti al loro interno
Controlla se tutti gli elementi di l1 sono contenuti in l2 o meno *)
let rec is_contained l1 l2 = match l1 with
	| [] -> true
	| p::q -> if (list_contains l2 p) then (is_contained q l2) else false

(* Rimuove l'elemento x dalla lista l se presente, dà errore altrimenti *)
let rec list_remove l x = match l with
	| [] -> raise ValueError
	| p::q -> if (p = x) then q else p::(list_remove q x)

(* Calcola il massimo fra due elementi di tipo Int / Bool / String *)
let max (a,b) = match (a,b) with
	| (Int(p), Int(q)) -> if (compare p q) = 1 then a else b
	| (Bool(p), Bool(q)) -> if (compare p q) = 1 then a else b
	| (String(p), String(q)) -> if (compare p q) = 1 then a else b
	| _ -> failwith("Uncomparable values")

(* Calcola il minimo fra due elementi di tipo Int / Bool / String *)
let min (a,b) = match (a,b) with
	| (Int(p), Int(q)) -> if (compare p q) = 1 then b else a
	| (Bool(p), Bool(q)) -> if (compare p q) = 1 then b else a
	| (String(p), String(q)) -> if (compare p q) = 1 then b else a
	| _ -> failwith("Uncomparable values")

(* Calcola il massimo di una lista di elementi dello stesso tipo (TInt, TBool o TString) *)
let rec list_max t l = if (t = TInt || t = TBool || t = TString) then (match l with
	| [] -> raise ValueError
	| p::[] -> p
	| p::q::m -> max(p, list_max t (q::m))
) else raise TypeError

(* Calcola il massimo di una lista di elementi dello stesso tipo (TInt, TBool o TString) *)
let rec list_min t l = if (t = TInt || t = TBool || t = TString) then (match l with
	| [] -> raise ValueError
	| p::[] -> p
	| p::q::m -> min(p, list_min t (q::m))
) else raise TypeError




(* PRIMITIVE del linguaggio *)

(* Controlla se un numero è zero *)
let is_zero(x) = match (typecheck(TInt,x),x) with
	| (true, Int(v)) -> Bool(v = 0)
	| (_, _) -> raise TypeError

(* Uguaglianza fra interi; non dovrà essere accessibile *)
let int_eq(x,y) =   
match (typecheck(TInt,x), typecheck(TInt,y), x, y) with
  | (true, true, Int(v), Int(w)) -> Bool(v = w)
  | (_,_,_,_) -> raise TypeError

(* Somma fra interi; non dovrà essere accessibile *)	   
 let int_plus(x, y) = 
 match(typecheck(TInt,x), typecheck(TInt,y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v + w)
  | (_,_,_,_) -> raise TypeError

(* Differenza fra interi; non dovrà essere accessibile *)
let int_sub(x, y) = 
 match(typecheck(TInt,x), typecheck(TInt,y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v - w)
  | (_,_,_,_) -> raise TypeError

(* Prodotto fra interi; non dovrà essere accessibile *)
let int_times(x, y) = match(typecheck(TInt,x), typecheck(TInt,y), x, y) with
 	| (true, true, Int(v), Int(w)) -> Int(v * w)
  	| (_,_,_,_) -> raise TypeError

(* Potenza fra interi; non dovrà essere accessibile *)
let int_pow(x,y) = match (typecheck(TInt,x), typecheck(TInt,y), x, y) with
	| (true, true, Int(v), Int(w)) -> Int(pow v w)
	|(_,_,_,_) -> raise TypeError

let less_than(x, y) = match (typecheck(TInt,x), typecheck(TInt,y), x, y) with
	| (true, true, Int(v), Int(w)) -> Bool(v < w)
	| (_,_,_,_) -> raise TypeError

let greater_than(x, y) = match (typecheck(TInt,x), typecheck(TInt,y), x, y) with
	| (true, true, Int(v), Int(w)) -> Bool(v > w)
	| (_,_,_,_) -> raise TypeError

let bool_and(x,y) = match (typecheck(TBool,x), typecheck(TBool,y), x, y) with
	| (true, true, Bool(v), Bool(w)) -> Bool(v && w)
	| (_,_,_,_) -> raise TypeError

let bool_or(x,y) = match (typecheck(TBool,x), typecheck(TBool,y), x, y) with
	| (true, true, Bool(v), Bool(w)) -> Bool(v || w)
	| (_,_,_,_) -> raise TypeError

let bool_not(x) = match (typecheck(TBool,x), x) with
	| (true, Bool(v)) -> Bool(not(v))
	| (_,_) -> raise TypeError

(* Crea un nuovo insieme vuoto *)
let new_empty (t : tname) = Set(t,[])

(* Crea un nuovo insieme con un solo elemento *)
let new_singleton (t,e) = if typecheck(t,e) then Set(t, [e]) else raise TypeError

(* Crea un nuovo insieme partendo da una lista di elementi.
Soluzione adottata: provo a creare s e se è ok per i tipi allora lo passo, altrimenti do errore; sicuro che sia la migliore? *)
let new_of (t,l) = if checkNotEquals l then (let s = Set(t, l) in if typecheck(TSet(t), s) then s else raise TypeError) else raise ValueError

(* Verifica se un insieme è vuoto *)
let is_empty (x : evT) = match x with
	| Set(t,l) -> if (l = []) then Bool(true) else Bool(false)
	| _ -> raise ValueError

(* Non fa uso del typechecker: può essere un problema? *)
let set_contains(s,x) = let t = getType x in match s with
	| Set(t', l) -> if (t = t') then Bool(list_contains l x) else raise TypeError
	| _ -> raise ValueError

let rec set_is_subset (e1, e2) = match (e1, e2) with
	| (Set(t1, l1), Set(t2,l2)) -> if (t1 = t2) then Bool(is_contained l1 l2) else raise TypeError
	| _ -> raise ValueError

let rec set_insert(e1, e2) = match e1 with
	| Set(t,l) -> if typecheck(t,e2) then ( if list_contains l e2 then raise ValueError 
	else Set(t, e2::l)) else raise TypeError
	| _ -> raise ValueError

let rec set_remove(e1, e2) = match e1 with
	| Set(t,l) -> if typecheck(t,e2) then (if list_contains l e2 then Set(t, list_remove l e2) else raise ValueError ) else raise TypeError
	| _ -> raise ValueError

(* Massimo di un insieme di interi / stringhe / booleani *)
let rec set_getMax(e1) = match e1 with
	| Set(t, l) -> list_max t l
	| _ -> raise ValueError

(* Minimo di un insieme di interi / stringhe / booleani *)
let rec set_getMin(e1) = match e1 with
	| Set(t,l) -> list_min t l
	| _ -> raise ValueError




(* Valutazione del programma *)

(* Valuta un'espressione restituendo un tipo primitivo del linguaggio (evT) *)
let rec eval (e:exp) (s:evT env) = match e with
	| EInt(n) -> Int(n)
	| True -> Bool(true)
	| False -> Bool(false)
	| EString(s) -> String(s)
	| Den(i) -> (s i)

	| Times(e1,e2) -> int_times((eval e1 s), (eval e2 s))
	| Sum(e1, e2) -> int_plus((eval e1 s), (eval e2 s))
	| Sub(e1, e2) -> int_sub((eval e1 s), (eval e2 s))
	| Pow(e1,e2) -> int_pow((eval e1 s),(eval e2 s))
	
	| IsZero(e1) -> is_zero (eval e1 s)
	| Eq(e1, e2) -> int_eq((eval e1 s), (eval e2 s))
	| LessThan(e1, e2) -> less_than((eval e1 s),(eval e2 s))
	| GreaterThan(e1, e2) -> greater_than((eval e1 s),(eval e2 s))

	| And(e1, e2) -> bool_and((eval e1 s),(eval e2 s))
	| Or(e1, e2) -> bool_or((eval e1 s),(eval e2 s))
	| Not(e1) -> bool_not(eval e1 s)

	| IfThenElse(e1,e2,e3) -> let g = eval e1 s in (* PROBLEMA: Ma così non si sa che tipo hanno le espressioni e2 ed e3; andrebbe introdotta una getType *)
		(match (typecheck(TBool, g), g) with
			| (true, Bool(true)) -> eval e2 s
			| (true, Bool(false)) -> eval e3 s
			| (_, _) -> raise ValueError
		)
	| Let(i, e, ebody) -> eval ebody (bind s i (eval e s))
	| Fun(arg, ebody) -> Closure(arg,ebody,s)
	| Letrec(f, arg, fBody, leBody) -> 
	let benv = bind (s) (f) (RecClosure(f, arg, fBody,s)) in
		eval leBody benv
	| Apply(eF, eArg) ->
		let fclosure = eval eF s in 
			(match fclosure with 
			| Closure(arg, fbody, fDecEnv) ->
				let aVal = eval eArg s in
				let aenv = bind fDecEnv arg aVal in 
					eval fbody aenv
			| RecClosure(f, arg, fbody, fDecEnv) ->
				let aVal = eval eArg s in
				let rEnv = bind fDecEnv f fclosure in
				let aenv = bind rEnv arg aVal in 
						eval fbody aenv
			| _ -> raise ValueError)
	
	| Empty(t) -> new_empty(t)
	| Singleton(t, e1) -> let f = eval e1 s in new_singleton(t,f)
	| Of(t, l) -> let rec evalList k s = match k with
		|[] -> []
		|p::q -> (eval p s)::(evalList q s)
	in (let m = evalList l s in new_of(t,m))
	
	| IsEmpty(e1) -> let f = eval e1 s in is_empty(f) 
	| Contains(e1, e2) -> let f1 = eval e1 s in let f2 = eval e2 s in set_contains(f1, f2)
	| IsSubset(e1, e2) -> let f1 = eval e1 s in let f2 = eval e2 s in set_is_subset(f1, f2)
	| Insert(e1, e2) -> let f1 = eval e1 s in let f2 = eval e2 s in set_insert(f1, f2)
	| Remove(e1, e2) -> let f1 = eval e1 s in let f2 = eval e2 s in set_remove(f1,f2) 
	| GetMin(e1) -> let f1 = eval e1 s in set_getMin(f1) 
	| GetMax(e1) -> let f1 = eval e1 s in set_getMax(f1)
	| For_all(e1, e2) = let f1 = eval e1 s in let f2 = eval e2 s in 

(* Closure("x", Den("x") + Int 5, global_envt) *)
(* Ancora da implementare: 
	(* Operatori funzionali su insiemi *)
	 (* controlla se tutti gli elementi dell’insieme soddisfano la proprietà definita dal parametro “predicate” *)
	| Exists of exp*exp (* controlla se esiste almeno un elemento dell’insieme che soddisfa la proprietà definita dal parametro “predicate” *)
	| Filter of exp*exp (* restituisce l’insieme degli elementi dell’insieme che soddisfano la proprietà definita dal parametro “predicate” *)
	| Map of exp*exp (* restitusce l’insieme dei valori v tali che v = function(x) dove x appartiene a aSet *)
*)