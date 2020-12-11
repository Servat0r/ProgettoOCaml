(* Interprete di MiniCaml esteso per il progetto di PR2 *)

(* TIPI DEFINITI *)

(* Identificatori *)
type ide = string;;

(* tsub sono esattamente i tipi di dato ammissibili per un insieme: interi, stringhe e booleani *)
type tsub = TInt | TBool | TString

(* I tipi TInt ... TString sono dichiarati nuovamente per sfruttare l' "aliasing", si vedano upcast e downcast *)
type tname =  TInt | TBool | TString | TClosure | TRecClosure | TSet of tsub | TUnBound

(* Abstract Expressions = espressioni nella sintassi astratta, compongono l'Albero di Sintassi Astratta *)
type exp = EInt of int
		| True 
		| False
		| EString of string
		| Den of ide
		(* Operatori binari da interi a interi*)
		| Sum of exp * exp
		| Sub of exp * exp
		| Prod of exp * exp
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
		| Letrec of ide * ide  * exp * exp
		| Fun of ide * exp
		| Apply of exp * exp
		(* Costruttori di insiemi *)
		| Empty of tsub (* Insieme vuoto *)
		| Singleton of tsub*exp (* Insieme con un solo elemento *)
		| Of of tsub*setEl (* Insieme con uno o più elementi *)
		(* Operatori unari su insiemi*)
		| IsEmpty of exp 
		| GetMin of exp 
		| GetMax of exp
		(* Operatori binari su insiemi *)
		| Union of exp*exp
		| Intersection of exp*exp 
		| Difference of exp*exp 
		| Insert of exp*exp
		| Remove of exp*exp
		| Contains of exp*exp
		| IsSubset of exp*exp
		(* Operatori funzionali su insiemi *)
		| For_all of exp*exp 
		| Exists of exp*exp 
		| Filter of exp*exp 
		| Map of exp*exp
		(* Sintassi astratta per i valori degli elementi di un set *)
		and setEl = Void | Item of exp*setEl

(* Ambiente polimorfo; avremo un solo ambiente (globale), eventualmente copiato e passato ad altre funzioni *)
type 't env = string -> 't

(* Evaluation types = tipi primitivi esprimibili; le chiusure sono ricorsive di default *)
type evT = Int of int 
	| Bool of bool 
	| String of string 
	| Closure of ide * exp * evT env 
	| RecClosure of ide * ide * exp * evT env
	| Set of tsub*(evT list)
	| UnBound

(* Errori a runtime *)
exception RuntimeError of string

(* Una mappa da evT a tname che a ogni valore col suo descrittore di tipo associa il nome del tipo *)
let (getType : evT -> tname) = function x -> match x with
	| Int(n) -> TInt
	| Bool(b) -> TBool
	| String(s) -> TString
	| Closure(i,e,en) -> TClosure
	| RecClosure(i,j,e,en) -> TRecClosure
	| Set(t,l) -> TSet(t)
	| UnBound -> TUnBound

(* Funzione di upcasting da tsub a tname *)
let (upcast : tsub -> tname) = function x -> match x with
	| TInt -> TInt
	| TBool -> TBool
	| TString -> TString

(* Funzione di downcasting da tname a tsub *)
let (downcast : tname -> tsub) = function x -> match x with
	| TInt -> TInt
	| TBool -> TBool
	| TString -> TString
	| _ -> raise ( RuntimeError "Cannot downcast")



(* Ambiente vuoto *)
let emptyenv = function x -> UnBound


(* Type-checking *)
let typecheck ((x, y) : (tname*evT)) = match x with
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
		|TSet(tn) ->
			(match y with
				| Set(t, l) -> (if (tn = t) then 
					let rec sameType (t : tname) (l : evT list) = match l with
						| [] -> true
						| p::q -> let t' = getType p in (if (t = t') then sameType t q else false)
					in sameType (upcast t) l else false)
				| _ -> false
				)
        |TClosure -> 
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

(* Binding fra una stringa x e un valore primitivo evT *)
let bind (s: evT env) (x: string) (v: evT) = function (i: string) -> if (i = x) then v else (s i)



(* UTILITIES per le primitive del linguaggio (NON sono primitive!) *)

(* Controlla se una lista contiene o meno l'elemento dato *)
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
	| [] -> raise ( RuntimeError "")
	| p::q -> if (p = x) then q else p::(list_remove q x)

(* Calcola il massimo fra due elementi di tipo TInt / TBool / TString *)
let max (a,b) = match (a,b) with
	| (Int(p), Int(q)) -> if (compare p q) = 1 then a else b
	| (Bool(p), Bool(q)) -> if (compare p q) = 1 then a else b
	| (String(p), String(q)) -> if (compare p q) = 1 then a else b
	| _ -> raise (RuntimeError "Uncomparable values")

(* Calcola il minimo fra due elementi di tipo TInt / TBool / TString *)
let min (a,b) = match (a,b) with
	| (Int(p), Int(q)) -> if (compare p q) = 1 then b else a
	| (Bool(p), Bool(q)) -> if (compare p q) = 1 then b else a
	| (String(p), String(q)) -> if (compare p q) = 1 then b else a
	| _ -> raise (RuntimeError "Uncomparable values")

(* Calcola il massimo di una lista di elementi dello stesso tipo (TInt, TBool o TString) *)
let rec list_max (t : tsub) l = match l with
	| [] -> raise ( RuntimeError "")
	| p::[] -> p
	| p::q::m -> max(p, list_max t (q::m))


(* Calcola il massimo di una lista di elementi dello stesso tipo (TInt, TBool o TString) *)
let rec list_min (t : tsub) l = match l with
	| [] -> raise ( RuntimeError "")
	| p::[] -> p
	| p::q::m -> min(p, list_min t (q::m))



(* PRIMITIVE del linguaggio *)

(* Controlla se un numero è zero *)
let is_zero(x) = match (typecheck(TInt,x),x) with
	| (true, Int(v)) -> Bool(v = 0)
	| (_, _) -> raise ( RuntimeError "Wrong type")

(* Uguaglianza fra interi *)
let int_eq(x,y) =   
match (typecheck(TInt,x), typecheck(TInt,y), x, y) with
  | (true, true, Int(v), Int(w)) -> Bool(v = w)
  | (_,_,_,_) -> raise ( RuntimeError "Wrong type")

(* Somma fra interi *)	   
 let int_plus(x, y) = 
 match(typecheck(TInt,x), typecheck(TInt,y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v + w)
  | (_,_,_,_) -> raise ( RuntimeError "Wrong type")

(* Differenza fra interi *)
let int_sub(x, y) = 
 match(typecheck(TInt,x), typecheck(TInt,y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v - w)
  | (_,_,_,_) -> raise ( RuntimeError "Wrong type")

(* Prodotto fra interi *)
let int_times(x, y) = match(typecheck(TInt,x), typecheck(TInt,y), x, y) with
 	| (true, true, Int(v), Int(w)) -> Int(v * w)
  	| (_,_,_,_) -> raise ( RuntimeError "Wrong type")


let less_than(x, y) = match (typecheck(TInt,x), typecheck(TInt,y), x, y) with
	| (true, true, Int(v), Int(w)) -> Bool(v < w)
	| (_,_,_,_) -> raise ( RuntimeError "Wrong type")

let greater_than(x, y) = match (typecheck(TInt,x), typecheck(TInt,y), x, y) with
	| (true, true, Int(v), Int(w)) -> Bool(v > w)
	| (_,_,_,_) -> raise ( RuntimeError "Wrong type")


let bool_and(x,y) = match (typecheck(TBool,x), typecheck(TBool,y), x, y) with
	| (true, true, Bool(v), Bool(w)) -> Bool(v && w)
	| (_,_,_,_) -> raise ( RuntimeError "Wrong type")

let bool_or(x,y) = match (typecheck(TBool,x), typecheck(TBool,y), x, y) with
	| (true, true, Bool(v), Bool(w)) -> Bool(v || w)
	| (_,_,_,_) -> raise ( RuntimeError "Wrong type")

let bool_not(x) = match (typecheck(TBool,x), x) with
	| (true, Bool(v)) -> Bool(not(v))
	| (_,_) -> raise ( RuntimeError "Wrong type")

(* Crea un nuovo insieme vuoto *)
let new_empty (t : tsub) = Set(t,[])

(* Crea un nuovo insieme con un solo elemento *)
let new_singleton ((t, e) : (tsub*evT)) = if typecheck(upcast t,e) then Set(t, [e]) else raise ( RuntimeError "Wrong type")

(* Crea un nuovo insieme partendo da una lista di elementi. *)
let new_of ((t , l) : (tsub*(evT list))) = if checkNotEquals l then (let s = Set(t, l) in 
	if typecheck(TSet(t), s) then s else raise ( RuntimeError "Wrong type")) else raise ( RuntimeError "Duplicated values!")

(* Verifica se un insieme è vuoto *)
let is_empty (x : evT) = let empty_list l = match l with
	| [] -> true
	| _ -> false
	in match x with
		| Set(t,l) -> Bool(empty_list l)
		| _ -> raise ( RuntimeError "Wrong type")

(* Verifica se un insieme contiene un elemento dato *)
let set_contains(s,x) = match s with
	| Set(t, l) -> if typecheck(upcast t, x) then Bool(list_contains l x) else raise ( RuntimeError "Wrong type")
	| _ -> raise ( RuntimeError "Wrong type")

(* Verifica se un insieme è sottoinsieme di un altro insieme *)
let set_is_subset (s1, s2) = match s1 with
	| Set(t,l1) -> (match(typecheck(TSet(t),s2),s2) with
		| (true, Set(t,l2)) -> Bool(is_contained l1 l2)
		| (_,_) -> raise ( RuntimeError "Wrong type")
	)
	| _ -> raise ( RuntimeError "Wrong type")

(* Inserisce un elemento in un insieme *)
let set_insert(e1, e2) = match e1 with
	| Set(t,l) -> if typecheck(upcast t,e2) then ( if list_contains l e2 then Set(t,l) else Set(t, e2::l)) 
		else raise ( RuntimeError "Wrong type")
	| _ -> raise ( RuntimeError "Wrong type")

(* Rimuove un elemento da un insieme *)
let set_remove(e1, e2) = match e1 with
	| Set(t,l) -> if typecheck(upcast t,e2) then (if list_contains l e2 then Set(t, list_remove l e2) else raise ( RuntimeError "Not existing element!") ) 
		else raise ( RuntimeError "Wrong type")
	| _ -> raise ( RuntimeError "Wrong type")

(* Massimo di un insieme di interi / stringhe / booleani *)
let set_getMax(e1) = match e1 with
	| Set(t, l) -> list_max t l
	| _ -> raise ( RuntimeError "Wrong type")

(* Minimo di un insieme di interi / stringhe / booleani *)
let set_getMin(e1) = match e1 with
	| Set(t,l) -> list_min t l
	| _ -> raise ( RuntimeError "Wrong type")



(* Valuta un'espressione restituendo un tipo primitivo del linguaggio (evT) *)
let rec eval (e:exp) (s:evT env) : evT = match e with
	| EInt(n) -> Int(n)
	| True -> Bool(true)
	| False -> Bool(false)
	| EString(s) -> String(s)
	| Den(i) -> (s i)

	| Prod(e1,e2) -> int_times((eval e1 s), (eval e2 s))
	| Sum(e1, e2) -> int_plus((eval e1 s), (eval e2 s))
	| Sub(e1, e2) -> int_sub((eval e1 s), (eval e2 s))
	
	| IsZero(e1) -> is_zero (eval e1 s)
	| Eq(e1, e2) -> int_eq((eval e1 s), (eval e2 s))
	| LessThan(e1, e2) -> less_than((eval e1 s),(eval e2 s))
	| GreaterThan(e1, e2) -> greater_than((eval e1 s),(eval e2 s))

	| And(e1, e2) -> bool_and((eval e1 s),(eval e2 s))
	| Or(e1, e2) -> bool_or((eval e1 s),(eval e2 s))
	| Not(e1) -> bool_not(eval e1 s)

	| IfThenElse(e1,e2,e3) -> let g = eval e1 s in (match (typecheck(TBool,g),g) with
		|(true, Bool(true)) -> eval e2 s
		|(true, Bool(false)) -> eval e3 s
		|(_,_) -> raise ( RuntimeError "Wrong type")
	)
	(* let g = eval e1 s in (match typecheck(TBool, g) with
		| true -> let f2 = eval e2 s in let f3 = eval e3 s in let t = getType f2 in let t' = getType f3 in (if t = t') then 
			(if (g = Bool(true)) then f2 else f3) else raise RuntimeError("The two branches don't have the same type")
		| false -> raise RuntimeError("Non-boolean guard")
	)
	*)
	| Let(i, e, ebody) -> eval ebody (bind s i (eval e s))
	| Fun(arg, ebody) -> Closure(arg,ebody,s)
	| Letrec(f, arg, fBody, leBody) ->
	let benv = bind (s) (f) (RecClosure(f, arg, fBody,s)) in
		eval leBody benv
	| Apply(eF, eArg) ->
		let fclosure = eval eF s in (match fclosure with 
			| Closure(arg, fbody, fDecEnv) -> 
				let aVal = eval eArg s in 
				let aenv = bind fDecEnv arg aVal in 
				eval fbody aenv 
			| RecClosure(f, arg, fbody, fDecEnv) -> 
				let aVal = eval eArg s in
				let rEnv = bind fDecEnv f fclosure in
				let aenv = bind rEnv arg aVal in 
				eval fbody aenv
			| _ -> raise ( RuntimeError "Wrong type")
			)
	| Empty(t) -> new_empty(t)
	| Singleton(t, e1) -> let f = eval e1 s in new_singleton(t,f)
	| Of(t, l) -> let rec evalList k s = match k with
		|Void -> []
		|Item(p,q) -> let r = eval p s in let ls = evalList q s in if list_contains ls r then ls else r::ls
	in (let m = evalList l s in new_of(t,m))

	| Union(e1, e2) -> let f1 = eval e1 s in let f2 = eval e2 s in (match f1 with
		| Set(t, l) -> (match (typecheck(TSet(t),f2),f2) with
			|(true, Set(t,m)) -> let rec list_union(l,m) = match l with
				|[] -> m
				|p::q -> if list_contains m p then list_union(q,m) else list_union(q,p::m)
		        in Set(t, list_union(l,m))
			|(_,_) -> raise ( RuntimeError "Wrong type"))
		| _ -> raise ( RuntimeError "Wrong type")
	)

	| Intersection(e1, e2) -> let f1 = eval e1 s in let f2 = eval e2 s in (match f1 with
		| Set(t,l) -> (match (typecheck(TSet(t),f2),f2) with
			|(true, Set(t,m)) -> let rec list_intersection(l,m) = match l with
				|[] -> []
				|p::q -> if list_contains m p then p::list_intersection(q,m) else list_intersection(q,m)
				in Set(t, list_intersection(l,m))
			| (_,_) -> raise ( RuntimeError "Wrong type"))
		| _ -> raise ( RuntimeError "Wrong type")
	)

	| Difference(e1, e2) -> let f1 = eval e1 s in let f2 = eval e2 s in (match f1 with
		| Set(t,l) -> (match (typecheck(TSet(t),f2),f2) with
			| (true, Set(t,m)) -> let rec list_difference(l,m) = match l with
				|[] -> []
				|p::q -> if list_contains m p then list_difference(q,m) else p::list_difference(q,m)
				in Set(t, list_difference(l,m))
			| (_,_) -> raise ( RuntimeError "Wrong type"))
		| _ -> raise ( RuntimeError "Wrong type")
	)
	
	| IsEmpty(e1) -> let f = eval e1 s in is_empty(f) 
	| Contains(e1, e2) -> let f1 = eval e1 s in let f2 = eval e2 s in set_contains(f1, f2)
	| IsSubset(e1, e2) -> let f1 = eval e1 s in let f2 = eval e2 s in set_is_subset(f1, f2)
	| Insert(e1, e2) -> let f1 = eval e1 s in let f2 = eval e2 s in set_insert(f1, f2)
	| Remove(e1, e2) -> let f1 = eval e1 s in let f2 = eval e2 s in set_remove(f1,f2) 
	| GetMin(e1) -> let f1 = eval e1 s in set_getMin(f1) 
	| GetMax(e1) -> let f1 = eval e1 s in set_getMax(f1)

	| For_all(e1, e2) -> let rec forall_list(f,l) = match l with
		|[] -> Bool(true)
		|p::q -> ( match f with
			|Closure(arg,fbody,fDecEnv) -> 
				let fExEnv = bind fDecEnv arg p in
				let res = eval fbody fExEnv in
				if (res = Bool(true)) then forall_list(f,q)
				else if (res = Bool(false)) then Bool(false)
				else raise ( RuntimeError "Wrong type")
			|RecClosure(g, arg, fbody, fDecEnv) ->
				let fpExEnv = bind fDecEnv arg p in
				let fExEnv = bind fpExEnv g f in
				let res = eval fbody fExEnv in
				if res = Bool(true) then forall_list(f,q)
				else if res = Bool(false) then Bool(false)
				else raise ( RuntimeError "Wrong type")
			| _ -> raise ( RuntimeError "Wrong type")
			)
		in let fclosure = eval e1 s in let fset = eval e2 s in (match fset with
			| Set(t,l) -> forall_list(fclosure,l)
			| _ -> raise ( RuntimeError "Wrong type")
		)

	| Exists(e1, e2) -> let rec exists_list(f,l) = match l with
		|[] -> Bool(false)
		|p::q -> ( match f with
			|Closure(arg,fbody,fDecEnv) -> 
				let fExEnv = bind fDecEnv arg p in
				let res = eval fbody fExEnv in
				if res = Bool(true) then Bool(true)
				else if res = Bool(false) then exists_list(f,q)
				else raise ( RuntimeError "Wrong type")
			|RecClosure(g, arg, fbody, fDecEnv) ->
				let fpExEnv = bind fDecEnv arg p in
				let fExEnv = bind fpExEnv g f in
				let res = eval fbody fExEnv in
				if res = Bool(true) then Bool(true)
				else if res = Bool(false) then exists_list(f,q)
				else raise ( RuntimeError "Wrong type")
			| _ -> raise ( RuntimeError "")
			)
		in let fclosure = eval e1 s in let fset = eval e2 s in (match fset with
			| Set(t,l) -> exists_list(fclosure,l)
			| _ -> raise ( RuntimeError "Wrong type")
		)

	| Filter(e1, e2) -> let rec filter_list(f,l) = match l with
		|[] -> []
		|p::q -> ( match f with
			|Closure(arg,fbody,fDecEnv) -> 
				let fExEnv = bind fDecEnv arg p in
				let res = eval fbody fExEnv in
				(if (res = Bool(true)) then p::(filter_list(f,q))
				else if res = Bool(false) then filter_list(f,q)
				else raise ( RuntimeError "Wrong type"))
			|RecClosure(g, arg, fbody, fDecEnv) ->
				let fpExEnv = bind fDecEnv arg p in
				let fExEnv = bind fpExEnv g f in
				let res = eval fbody fExEnv in
				if res = Bool(true) then p::(filter_list(f,q))
				else if res = Bool(false) then filter_list(f,q)
				else raise ( RuntimeError "Wrong type")
			| _ -> raise ( RuntimeError "Wrong type")
			)
		in let fclosure = eval e1 s in let fset = eval e2 s in (match fset with
			| Set(t,l) -> Set(t,filter_list(fclosure,l))
			| _ -> raise ( RuntimeError "Wrong type")
		)
	
	| Map(e1, e2) -> let rec map_list(f,l) = match l with
		|[] -> []
		|p::q -> (match f with
			| Closure(arg,fbody,fDecEnv) -> 
				let tail = map_list(f,q) in
				let fExEnv = bind fDecEnv arg p in
				let res = eval fbody fExEnv in
				if list_contains tail res then tail else res::tail			
			| RecClosure(g,arg,fbody,fDecEnv) ->
				let tail = map_list(f,q) in
				let fpExEnv = bind fDecEnv arg p in
				let fExEnv = bind fpExEnv g f in
				let res = eval fbody fExEnv in
				if list_contains tail res then tail else res::tail
			| _ -> raise ( RuntimeError "Wrong type")
		)
		in let fclosure = eval e1 s in let fset = eval e2 s in (match fset with
			| Set(t,l) -> (if l = [] then raise ( RuntimeError "Cannot apply on an empty set!") (* Non possiamo applicare la fclosure a un insieme vuoto *)
			else let m = map_list(fclosure,l) in (* Sappiamo che perlomeno non ci sono elementi duplicati *)
			let t' = getType (List.hd m) in 
			(try let ts = downcast t' in let r = Set(ts, m) in if typecheck(TSet(ts), r) then r else raise ( RuntimeError "Wrong type")
			with  err -> raise ( RuntimeError "Cannot downcast")))
			| _ -> raise ( RuntimeError "Wrong type")
		)