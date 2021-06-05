type ide = string;;						(*identificatori*)

type bVal = 							(*valori base*) 
	| Int of int
	| Bool of bool
	| Tuple of bVal list
and fVal = 								(*valori funzione*)
	| Fun of ide * exp
and value = 							(*valori generici*)
	| Bval of bVal
	| Fval of fVal
and exp = 
	| Ide of ide 						(*identificatori*)
	| Val of value 						(*valori*)
	| Add of exp * exp 					(*operatori binari*)
	| Sub of exp * exp
	| Mul of exp * exp
	| Div of exp * exp
	| Opp of exp 						(*operatore unario: opposto di un intero*)
	| Equ of exp * exp 					(*operatori binari booleani*)
	| Less of exp * exp
	| More of exp * exp
	| And of exp * exp 					
	| Or of exp * exp
	| Not of exp 						(*operatore unario booleano*)
	| IfThenElse of exp * exp * exp 	(*if then else*)
	| In of exp * bVal 					(*contains tuple val*)
	| IsEmpty of bVal 					(*empty tuple*)
	| Slice of bVal * int * int 		(*slice tuple*)
	| Access of bVal * int 				(*n-th element tuple*)
	| Let of exp * exp * exp 			(*dichiarazione*)
	| FunApp of ide * exp 				(*applicazione di funzione*)
	| For of ide * bVal * exp 			(*for su tupla*)
;;



(*definizione eccezioni*)
exception InvalidVariable;;
exception InvalidTuple;;
exception InvalidIndex;;
exception InvalidIdentifier;;
exception WrongType;;

(*controlla se l'ide x è presente nell'ambiente env*)
let rec lookup env x =
    match env with 
    | []        -> raise InvalidVariable
    | (y, v)::ys-> if (x=y) then v 
    						else lookup ys x
;;

(*controlla se x è contenuto nella tupla tup*)
let isIn tup x = 
	let rec contains lista x = match lista with
		| [] 	-> Bool(false)
		| y::ys -> if (x = y) then Bool(true)
							  else contains ys x	
	in
	match tup with
		| Tuple(y) 	-> contains y x
		| _ 		-> raise InvalidTuple
;;

(*controlla se la tupla è vuota*)
let isEmptyT tup = 
	let rec empL lista = match lista with
		| [] 	-> Bool(true)
		| _ 	-> Bool(false)
	in
	match tup with
		|Tuple(y) 	-> empL y
		| _ 		-> raise InvalidTuple
;;

(*trova la lunghezza della lista*)
let rec length lista = match lista with
	| [] -> 0
	| x::xs -> 1 + (length xs)
;; 

(*inverte la lista*)
let rec reverse lista = match lista with
	| [] -> []
	| y::ys -> (reverse ys)@[y]
;; 

(*restituisce i primi n elementi della lista*)
let rec take lista n = 
	if (n=0) then [] else match lista with
		| [] -> []
		| x::xs -> x::(take xs (n-1))
;;

(*elimina i primi n elementi della lista*)
let rec drop lista n =
	if (n=0) then lista else match lista with
		| [] -> []
		| x::xs -> drop xs (n-1)
;;	

(*trova i valori compresi tra gli indici i e j nella tupla*)
let slice tup i j =
	let sliceL lista a b = 
		let lung = length lista in
			if ((a>=0)&&(b>=0)) then take (drop lista a) (b-a+1)
			else if((a<0)&&(b<0)) then (let newa = lung+b in
											let newb = lung+a in
												reverse(take (drop lista newa) (newb-newa+1))
										)
							  	  else raise InvalidIndex
	in
	match tup with
		| Tuple(y) 	-> sliceL y i j
		| _			-> raise InvalidTuple 
;;

(*restituisce l'i-esimo elemento della tupla*)
let getT tup n = 
	let rec getL lista index = match lista with
		| [] -> raise InvalidTuple
		| x::xs when (index = 0) -> x
		| x::xs when (index > 0) -> getL xs (index-1)
		| x::xs when (index < 0) -> let els = length lista in
										let newindex = (els + index) in 
											getL lista newindex
		| _ -> raise InvalidIndex
	in
	match tup with
		| Tuple(y) 	-> getL y n
		| _ 		-> raise InvalidTuple
;;

(*controlla se la funzione chiamata ide è presente in fenv*)
let searchF id fenv =
	let rec containsF lista x = match lista with
		| [] -> failwith "emptyFunEnv"
		| (y,v)::ys -> if (id=y) then v
								 else containsF ys x
	in
	match id with
		| Ide(y) -> containsF fenv id
		| _ -> raise InvalidIdentifier
;;

(*filtra una lista, restituendo solo gli elementi che soddisfano p*)
let rec filter p lista = match lista with
	| [] -> []
	| x::xs -> if (p x) then x::(filter p xs)
						else (filter p xs)
;;

(*controlla se il valore x è un Int*)
let isInteger (x: bVal) = match x with
	| Int(i) -> true
	| _      -> false
;;

(*controlla se il valore x è un Bool*)
let isBoolean (x: bVal) = match x with
	| Bool(b) -> true
	| _       -> false
;;


(*VALUTAZIONE ESPRESSIONI*)
let rec eval (e:exp) env fenv = match e with
	| Ide(id) 		-> lookup env e
	| Val(v) 		-> (match v with
							| Bval(v1) -> v1
							| _ -> failwith "Invalid value" 
						)
	| Add (e1, e2) 	-> 	(let v1 = eval e1 env fenv in
							let v2 = eval e2 env fenv in
						match (v1,v2) with
							| (Int(a),Int(b)) 	-> Int(a+b)
							| (_,_) 			-> raise WrongType
						)
	| Sub (e1, e2)	-> 	(let v1 = eval e1 env fenv in
							let v2 = eval e2 env fenv in
						match (v1,v2) with
							| (Int(a),Int(b)) 	-> Int(a-b)
							| (_,_) 			-> raise WrongType
						)
	| Mul (e1, e2)	-> 	(let v1 = eval e1 env fenv in
							let v2 = eval e2 env fenv in
						match (v1,v2) with
							| (Int(a),Int(b)) 	-> Int(a*b)
							| (_,_) 			-> raise WrongType
						)
	| Div (e1, e2)	->	(let v1 = eval e1 env fenv in
							let v2 = eval e2 env fenv in
						match (v1,v2) with
							| (Int(a),Int(b)) 	-> Int(a/b)
							| (_,_) 			-> raise WrongType
						)
	| Opp (e1)      -> 	(let v1 = eval e1 env fenv in
						match v1 with
							| Int(a) 	-> Int(-1*a)
							| _ 		-> raise WrongType
						)
	| Equ (e1, e2)	-> 	if(eval e1 env fenv) = (eval e2 env fenv) then Bool(true) else Bool(false)
	| Less(e1, e2)	->	if(eval e1 env fenv) < (eval e2 env fenv) then Bool(true) else Bool(false)
	| More(e1, e2)	->	if(eval e1 env fenv) > (eval e2 env fenv) then Bool(true) else Bool(false)
	| And (e1, e2) 	->	if(eval e1 env fenv) = Bool(true) then eval e2 env fenv else Bool(false)
	| Or  (e1, e2) 	->	if(eval e1 env fenv) = Bool(true) then Bool(true) else (eval e2 env fenv) 
	| Not (e1) 		->	if(eval e1 env fenv) = Bool(false) then Bool(true) else Bool(false)	
	| IfThenElse(guard, e1, e2) -> if(eval guard env fenv) = Bool(true) then (eval e1 env fenv)
																 	    else (eval e2 env fenv)
	| In(e,tup) 	-> 	let v = eval e env [] in
							(match tup with
								| Tuple(y) -> isIn tup v
								| _ -> raise InvalidTuple
							)
	| IsEmpty(tup)   -> (match tup with
							| Tuple(y) -> isEmptyT tup
							| _ -> raise InvalidTuple
					    )
	| Slice(tup,i,j) -> (match tup with
							| Tuple(y) -> Tuple(slice tup i j)
							| _ -> raise InvalidTuple
					    )
	| Access(tup,n)	 -> (match tup with
							| Tuple(y) -> getT tup n
							| _ -> raise InvalidTuple
					    )
	| Let(var,e,body)-> let env2 = bind var e env in
							eval body env2 []
	| FunApp(name,e) -> let v1 = eval e env [] in
							let (param,body,fenv2) = searchF (Ide(name)) fenv in
								let env2 = bind param (Val(Bval(v1))) fenv2 in
									eval body env2 fenv
	| For(i, tup, e) -> (match tup with
							| Tuple(y) -> (match i with
											| ("int")  -> let t = filter isInteger y in
															Tuple( applyExp (Ide("int")) t e env fenv )
											| ("bool") -> let t = filter isBoolean y in
															Tuple( applyExp (Ide("bool")) t e env fenv )
											| _        -> raise WrongType
										  )
							| _        -> raise InvalidTuple
						)
(*effettua il binding dell'identificatore i*)
and bind i e env = match i with
	| Ide(x) -> (i,eval e env [])::env
	| _ -> raise InvalidIdentifier
(*funzione che applica l'espressione e alla lista*)
and applyExp i lista e env fenv = match lista with
	| []     -> []
	| y::ys  -> let rec recApply (i,lista,e) env fenv = match lista with
					| [] -> []
					| x::xs -> let env2 = bind i (Val(Bval(x))) env in 
									let newval = eval e env2 fenv in
										let leftover = recApply (i,xs,e) env fenv in
											newval::leftover
			   	in recApply (i,lista,e) env fenv
;;


(*--------------------TEST--------------------*)
(*definizione ambiente vuoto delle espressioni*)
let emptyEnv = [];;
(*definizione ambiente vuoto delle espressioni delle funzioni*)
let emptyFunEnv = [];;

(*Ide -> controllo binding identificatori: x=29*)
eval (Ide("x")) [(Ide("x"),Int(29))] emptyFunEnv;; 
(*Ide -> controllo binding identificatori: InvalidVariable Exception*)
eval (Ide("y")) emptyEnv emptyFunEnv;;
(*Val -> controllo valutazione valori: 2016*)
eval (Val(Bval(Int(2016)))) [] emptyFunEnv;;
(*Add -> operazione somma interi: 2+2=4 *)
eval (Add((Val(Bval(Int(2)))), Val(Bval(Int(2))))) emptyEnv emptyFunEnv;; 
(*Sub -> operazione differenza interi: 4-2=2 *)
eval (Sub((Val(Bval(Int(4)))), Val(Bval(Int(2))))) emptyEnv emptyFunEnv;; 
(*Mul -> operazione moltiplicazione interi: 5*2=10 *)
eval (Mul((Val(Bval(Int(5)))), Val(Bval(Int(2))))) emptyEnv emptyFunEnv;; 
(*Div -> operazione divisione interi: 10/2=5 *)
eval (Div((Val(Bval(Int(10)))), Val(Bval(Int(2))))) emptyEnv emptyFunEnv;; 
(*Opp -> calcolo opposto di un intero: 1*(-1)=-1 *)
eval (Opp(Val(Bval(Int(1))))) emptyEnv emptyFunEnv;; 
(*Add -> operazione somma: 2+true= WrongType Exception *)
eval (Add((Val(Bval(Int(2)))), Val(Bval(Bool(true))))) emptyEnv emptyFunEnv;; 

let tupeq = Tuple([Int(10);Bool(false);Tuple([Int(20);Bool(true)])]);;
(*Equ -> operatore = tuple:
tupla1: Tuple[Int 10: Bool false; Tuple[Int 20; Bool true]];
tupla2: Tuple[Int 10: Bool false; Tuple[Int 20; Bool true]];
risultato atteso: true*)
eval (Equ(Val(Bval(Tuple([Int(10);Bool(false);Tuple([Int(20);Bool(true)])]))), Val(Bval(Tuple([Int(10);Bool(false);Tuple([Int(20);Bool(true)])]))))) emptyEnv emptyFunEnv;; (*effettua il controllo di uguaglianza fra due tuple. Ret = Bool(true)*)
(*Less -> operatore < interi:
intero1: 2
intero2: 4
risultato atteso: 2<4 = true*)
eval (Less( Val(Bval(Int(2))), Val(Bval(Int(4))) )) emptyEnv emptyFunEnv;;
(*More -> operatore > interi:
intero1: 2
intero2: 10
risultato atteso: 2>4 = false*)
eval (More( Val(Bval(Int(2))), Val(Bval(Int(10))) )) emptyEnv emptyFunEnv;;

let envir = [(Ide("x"),Bool(true)); (Ide("y"),Bool(false))];;
(*And -> opeartore booleano
bool1: x=true
bool2: y=false
risultato atteso: (true)&&(false) = (false) *)
eval (And( Ide("x"), Ide("y") )) envir emptyFunEnv;;
(*Or -> opeartore booleano
bool1: x=true
bool2: y=false
risultato atteso: (true)||(false) = (true) *)
eval (Or( Ide("x"), Ide("y") )) envir emptyFunEnv;;
(*Not -> opeartore booleano
bool1: x=true
risultato atteso: ~(true) = (false) *)
eval (Not( Ide("x"))) envir emptyFunEnv;;

(*if then else: ramo then
risultato atteso: if(true) then 29 else 7    -> 29 *)
eval (IfThenElse(Ide("x"),Val(Bval(Int(29))), Val(Bval(Int(7)))))  envir emptyFunEnv;;
(*if then else: ramo else
risultato atteso: if(false) then 29 else 7   ->  7 *)
eval (IfThenElse(Ide("y"),Val(Bval(Int(29))), Val(Bval(Int(7)))))  envir emptyFunEnv;;

(*In(e, tup)
tup = Tuple([Int(10);Bool(false);Tuple([Int(20);Bool(true)])]) 
e = Tuple([Int(20);Bool(true)])
risultato atteso: true *)
eval (In ( Val(Bval(Tuple([Int(20);Bool(true)]))), Tuple([Int(10);Bool(false);Tuple([Int(20);Bool(true)])]))) emptyEnv emptyFunEnv;;
(*In(e, tup)
tup = Tuple([Int(10);Bool(false);Tuple([Int(20);Bool(true)])]) 
e = [Int 29]
risultato atteso: false *)
eval (In ( Val(Bval(Int(29))), Tuple([Int(10);Bool(false);Tuple([Int(20);Bool(true)])]))) emptyEnv emptyFunEnv;;

(*IsEmpty(tup)
tup = []
risultato atteso: true *)
eval( IsEmpty( Tuple([]))) emptyEnv emptyFunEnv;;
(*IsEmpty(tup)
tup = Tuple([Int(29);Int(7)])
risultato atteso: false *)
eval( IsEmpty( Tuple([Int(29);Int(7)]))) emptyEnv emptyFunEnv;;

(*Slice(tup,i,j)
tup = [Int 1; Int 2; Int 3; Int 4; Int 5];
(i,j) = (1,3) 
risultato atteso: Tuple [Int 2; Int 3; Int 4]; *)
eval( Slice( Tuple([Int(1);Int(2);Int(3);Int(4);Int(5)]), 1, 3)) emptyEnv emptyFunEnv;;
(*Slice(tup,i,j)
tup = [Int 1; Int 2; Int 3; Int 4; Int 5];
(i,j) = (-2,-4) 
risultato atteso: Tuple [Int 4; Int 3; Int 2]; *)
eval( Slice( Tuple([Int(1);Int(2);Int(3);Int(4);Int(5)]), (-2), (-4))) emptyEnv emptyFunEnv;;
(*Slice(tup,i,j)
tup = [Int 1; Int 2; Int 3; Int 4; Int 5];
(i,j) = (-2, 3) 
risultato atteso: exception: InvalidIndex *)
eval( Slice( Tuple([Int(1);Int(2);Int(3);Int(4);Int(5)]), (-2), 3)) emptyEnv emptyFunEnv;;

(*Access(tup, n)
tup = [Int 10; Int 20; Int 30; Int 40; Int 50];
n = 2;
risultato atteso: Int 30; *)
eval( Access( Tuple([Int(10);Int(20);Int(30);Int(40);Int(50)]), 2)) emptyEnv emptyFunEnv;;
(*Access(tup, n)
tup = [Int 10; Int 20; Int 30; Int 40; Int 50];
n = -2;
risultato atteso: Int 40; *)
eval( Access( Tuple([Int(10);Int(20);Int(30);Int(40);Int(50)]), (-2))) emptyEnv emptyFunEnv;;
(*Access(tup, n)
tup = [Int 10; Int 20; Int 30; Int 40; Int 50];
n = -29;
risultato atteso: InvalidIndex exception; *)
eval( Access( Tuple([Int(10);Int(20);Int(30);Int(40);Int(50)]), (-29))) emptyEnv emptyFunEnv;;

(*Let(var, e, body)
let y=3;;
let x=20 in
	x+y 
risultato atteso: Int 23; *)
let envir2 = [(Ide("y"),Int(3))];;
eval (Let(Ide("x"), Val(Bval(Int(20))), Add(Ide("y"),Ide("x")))) envir2 emptyFunEnv;;

(*FunApp(name,e)
funEnvir: let double x = x * 2;
risultato atteso: double(12) = 24 *)
let funEnvir = [(Ide("double"), (Ide("x"), Mul(Ide("x"), Val(Bval(Int(2))) ), emptyEnv))];;
eval (FunApp("double", Val(Bval(Int(12))))) emptyEnv funEnvir;;

(*For(i,tup,e)
ntup = Tuple([Int(1); Int(2); Int(3); Bool(false); Int(4); Int(5); Bool(true); Tuple([Int(29); Int(30)])]) 
e1: calcola il quadrato degli interi presenti nella tupla 
risultato atteso: Tuple([Int(1); Int(4); Int(9); Int(16); Int(25)]);  *)
let ntup = Tuple([Int(1); Int(2); Int(3); Bool(false); Int(4); Int(5); Bool(true); Tuple([Int(29); Int(30)])]);;
let e1 = Mul(Ide("int"), Ide("int"));;
eval (For( "int", ntup, e1)) emptyEnv emptyFunEnv;;
(*For(i,tup,e)
ntup = Tuple([Int(1); Int(2); Int(3); Bool(false); Int(4); Int(5); Bool(true); Tuple([Int(29); Int(30)])]) 
e2: applica l'operatore Not ai booleani presenti nella tupla 
risultato atteso: Tuple([Bool(true); Bool(false)]);  *)
let e2 = Not(Ide("bool"));;
eval (For( "bool", ntup, e2)) emptyEnv emptyFunEnv;;
(*For(i,tup,e)
tuplaPdf = Tuple([Int(23); Bool(true); Tuple([Int(45); Int(7)]); Bool(false)]); 
e3: applica l'operatore Not ai booleani presenti nella tupla 
risultato atteso: Tuple([Int(24)]);  *)
let tuplaPdf = Tuple([Int(23); Bool(true); Tuple([Int(45); Int(7)]); Bool(false)]);; 
let e3 = Add(Ide("int"), Val(Bval(Int(1))));;
eval (For( "int", tuplaPdf, e3)) emptyEnv emptyFunEnv;;