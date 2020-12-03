(* Interprete di MiniCaml: integrazione fra quanto avevo scritto in precedenza e quanto visto col Ferrari *)
(* Identificatori *)
type ide = string;;

(* Abstract Expressions = espressioni nella sintassi astratta, compongono l'Albero di Sintassi Astratta *)
type exp = EInt of int
		| True 
		| False
		| Den of ide
		| EString of string
		| Sum of exp * exp
		| Sub of exp * exp
		| Times of exp * exp
		| Pow of exp * exp 
		| IfThenElse of exp * exp * exp
		| Eq of exp * exp
		| Let of ide * exp * exp
		| Letrec of ide * ide * exp * exp
		| Fun of ide * exp
		| Apply of exp * exp

(* Ambiente polimorfo; avremo un solo ambiente (globale), eventualmente copiato e passato ad altre funzioni *)
type 't env = string -> 't

(* Evaluation types = tipi primitivi esprimibili; le chiusure sono ricorsive di default *)
type evT = Int of int | Bool of bool |String of string | Closure of ide * exp * evT env | RecClosure of ide * ide * exp * evT env | UnBound

exception TypeError
exception SyntaxError
exception ValueError
exception RuntimeError

(* Utilities: non si può accedere ad esse da fuori (capire come fare) *)

(* Ambiente globale iniziale; non dovrà essere accessibile *)
let global_envt = function x -> UnBound

(*
Per l'ambiente ne usiamo solo uno, per facilitare la creazione delle chiusure; di conseguenza, dovremo ricordarci dei nomi dei parametri
attuali di una funzione per ripristinare eventuali valori globali nel momento in cui si cancella un riferimento locale 
*)

(* Binding fra una stringa x e un valore primitivo evT; può essere usato per binding globali e locali, ovvero per lui NON è possibile
distinguere se lo si sta utilizzando in un assegnamento locale (Let o Letrec) o in uno globale (Bind): in quest'ultimo cqso i controlli
necessari (ad esempio per una funzione ricorsiva globale) li fa lui *)
let bind (s: evT env) (x: string) (v: evT) = function (i: string) -> if (i = x) then v else (s i)

(* Eliminazione di un nome *)
let del (s: evT env) (x: string) = function (i: string) -> if (i = x) then UnBound else (s i)

(* Type-checking; non dovrà essere accessibile *)
let typecheck (x, y) = match x with	
        | "int" -> 
            	(match y with 
                        | Int(u) -> true
                        | _ -> false
						)
        | "bool" -> 
            	(match y with 
                        | Bool(u) -> true
                        | _ -> false
						)
		| "string" ->
				(match y with
					|String(u) -> true
					| _ -> false
				)
        | _ -> raise TypeError


(* Potenza di un intero; non dovrà essere accessibile *)
let rec pow x n = if n = 0 then 1 else x * (pow x (n-1)) 

(* Uguaglianza fra interi; non dovrà essere accessibile *)
let int_eq(x,y) =   
match (typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Bool(v = w)
  | (_,_,_,_) -> raise RuntimeError

(* Somma fra interi; non dovrà essere accessibile *)	   
 let int_plus(x, y) = 
 match(typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v + w)
  | (_,_,_,_) -> raise RuntimeError

(* Differenza fra interi; non dovrà essere accessibile *)
let int_sub(x, y) = 
 match(typecheck("int",x), typecheck("int",y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v - w)
  | (_,_,_,_) -> raise RuntimeError

(* Prodotto fra interi; non dovrà essere accessibile *)
let int_times(x, y) = match(typecheck("int",x), typecheck("int",y), x, y) with
 	| (true, true, Int(v), Int(w)) -> Int(v * w)
  	| (_,_,_,_) -> raise RuntimeError

(* Potenza fra interi; non dovrà essere accessibile *)
let int_pow(x,y) = match (typecheck("int",x), typecheck("int",y), x, y) with
	| (true, true, Int(v), Int(w)) -> Int(pow v w)
	|(_,_,_,_) -> raise RuntimeError

let rec eval (e:exp) (s:evT env) = match e with
	| EInt(n) -> Int(n)
	| True -> Bool(true)
	| False -> Bool(false)
	| EString(s) -> String(s)

	| Eq(e1, e2) -> int_eq((eval e1 s), (eval e2 s))
	| Times(e1,e2) -> int_times((eval e1 s), (eval e2 s))
	| Sum(e1, e2) -> int_plus((eval e1 s), (eval e2 s))
	| Sub(e1, e2) -> int_sub((eval e1 s), (eval e2 s))
	| Pow(e1,e2) -> int_pow((eval e1 s),(eval e2 s))

	| IfThenElse(e1,e2,e3) -> let g = eval e1 s in (* PROBLEMA: Ma così non si sa che tipo hanno le espressioni e2 ed e3; andrebbe introdotta una getType *)
		(match (typecheck("bool", g), g) with
			| (true, Bool(true)) -> eval e2 s
			| (true, Bool(false)) -> eval e3 s
			| (_, _) -> raise ValueError
		)
	| Den(i) -> (s i)
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