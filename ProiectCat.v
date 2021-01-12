Require Import Strings.String.
Local Open Scope string_scope.
Scheme Equality for string.





Inductive ErrorNat :=
  | error_nat : ErrorNat (*ctor eroarea peste numerele naturale*,caz eroare*)
  | num : nat -> ErrorNat.  (*ctor num, cazul bun*)
Coercion num: nat >-> ErrorNat.

Inductive ErrorBool :=
  | error_bool : ErrorBool (*ctor eroare peste valorile boolene, cazul eroare*)
  | boolean : bool -> ErrorBool. (*ctor boolean, cazul bun*)
Coercion boolean: bool >-> ErrorBool.






Inductive Result :=
  | err_undecl : Result(*folosita in cod chiar daca nu a fost declarata*)
  | err_assign : Result (*atribuirea gresita a unei valori de tip bool cu o val de tip nat*)
  | default : Result (*dupa declararea unei var, var primeste o val default*)
  | res_nat : ErrorNat -> Result
  | res_bool : ErrorBool -> Result
  | res_string : string -> Result
  | err_str : Result.
  
Scheme Equality for Result.

Compute res_string "abdc".
Compute res_nat 20.







Definition Env := string -> Result. (*mapare de la un nume de variabile string catre un rezultat*)

(*env initial*)
Definition env : Env := fun x => err_undecl. (*toate variabilele noastre sunt undeclared,
 pana ce nu vor fi declarate, apoi vor primi valoare default, dupa declarare va fi posibila asignarea*)

Compute (env "x").






(*functie pentru a face egalitate pe tipuri, *)
Definition check_eq_over_types (t1 : Result) (t2 : Result) : bool :=
  match t1 with
    | err_undecl => match t2 with  (* putem updata variabila doar daca este delcarata*)
                    |err_undecl => true
                    | _ => false
                    end
    | err_assign => match t2 with 
                     | err_assign => true
                     | _ => false
                     end
    |default => match t2 with
                     | default => true
                     | _ => false
                      end
    |res_nat n  => match t2 with
                     | res_nat a => true
                     | _ => false
                      end
    |res_bool n => match t2 with
                     | res_bool a => true
                     | _ => false
                      end
   |res_string a => match t2 with
                     | res_string b => true
                     | _ => false
                      end
   |err_str => match t2 with
                | err_str => true
                | _ => false
                end
  end.
Compute (check_eq_over_types (res_bool (boolean true)) (res_nat 1)).
Compute (check_eq_over_types (res_nat 1)(res_nat 2)).









(*update la env*)
Definition update (env : Env ) ( x : string ) ( v : Result) : Env :=
  fun y =>
   if( eqb y x)
       then 
          (*daca variabila nu a fost initial declarata, si nu are valoarea default*)
          if ( andb (check_eq_over_types err_undecl (env y)) (negb (check_eq_over_types default v)))
          (*daca variabila este folosita si nu a fost inca declarata*)
          then err_undecl 
          else
              (*daca variabia a fost initial declarata si momentan are tipul default*)
             if( andb (check_eq_over_types err_undecl (env y))  (check_eq_over_types default v))
             then default
             else
                 (* daca variabila a fost atat declarata cat si initializata cu o valoare*)
                 if (orb (check_eq_over_types default (env y)) (check_eq_over_types v (env y)))
                 then v  (*valoare cu care vreau sa updataez variabila*)
                 (* daca valoare v nu este de acelasi tip cu variabila*)
                 else err_assign
   else (env y).

Notation "S [ V /' X ]" := (update S X V) (at level 0).



Compute (env "y").
Compute (update (update env "y" (default)) "y" (res_bool true) "y").
Compute (update (update env "x" (default)) "x" (res_string "abcde") "x").
Compute (update (update env "x" (default)) "x" (res_nat 19) "x").











(* op cu string*)
(*String Comparing*)
Notation "StringComp( a , b )" := (eqb a b)(at level 70).
Compute (StringComp( "abdasda" , "aasdac")).
Compute (StringComp( "a" , "a")).

(*Concatenarea*)
Fixpoint StringConc ( sa sb : string) : string :=
  match sa with
  | EmptyString => sb
  | String char s' => String char (StringConc s' sb)
  end.


Compute StringConc "abasdac"  "bcasdadasd".

(*Lungimea Stringurilor*)
Fixpoint StringLen (s1 : string) : nat :=
 match s1 with
 | EmptyString =>0
 | String c s1' => S (StringLen s1')
end.


Compute StringLen "asdasasr" .
















(*Expresii Aritmetice*)
Inductive AExp :=
  | avar: string -> AExp 
  | anum: ErrorNat -> AExp
  | aplus: AExp -> AExp -> AExp
  | asub: AExp -> AExp -> AExp
  | amul: AExp -> AExp -> AExp 
  | adiv: AExp -> AExp -> AExp 
  | amod: AExp -> AExp -> AExp
  | alung: string -> AExp.

(*coercions for numeric constants and variables*)
Coercion anum: ErrorNat >-> AExp.
Coercion avar: string >-> AExp. (* var ~> string*)

(*notatii pentru opertatii aritmetice*)
Notation "A +' B" := (aplus A B)(at level 50, left associativity).
Notation "A -' B" := (asub A B)(at level 50, left associativity).
Notation "A *' B" := (amul A B)(at level 48, left associativity).
Notation "A /' B" := (adiv A B)(at level 48, left associativity).
Notation "A %' B" := (amod A B)(at level 45, left associativity).
Notation "'StringLength' ( A )" := (alung A) (at level 50).


(* metode de calcul pentru operatii cu erori*)
Definition plus_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat (*primul argument error_nat, rez error_nat*)
    | _, error_nat => error_nat (*al 2 lea argument error_nat, rez error_nat*)
    | num v1, num v2 => num (v1 + v2) (*cazul bun, rez suma*)
    end.

Definition sub_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num n1, num n2 => if Nat.ltb n1 n2 (*prima val mai mica decat a 2 a, rez error_nat*)
                        then error_nat
                        else num (n1 - n2)
    end.

Definition mul_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | num v1, num v2 => num (v1 * v2)
    end.

Definition div_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat (*impartirea la 0, rez error_nat*)
    | num v1, num v2 => num (Nat.div v1 v2)
    end.

Definition mod_ErrorNat (n1 n2 : ErrorNat) : ErrorNat :=
  match n1, n2 with
    | error_nat, _ => error_nat
    | _, error_nat => error_nat
    | _, num 0 => error_nat (* modulo la 0, rez error_nat*)
    | num v1, num v2 => num (v1 - v2 * (Nat.div v1 v2))
    end.

Definition lung_ErrorNat (r:Result) : ErrorNat :=
match r with
 | res_string s => StringLen s
 | _ =>0
end.


Compute ( plus_ErrorNat 11 22 ).
Compute (div_ErrorNat (mul_ErrorNat 22 11) (sub_ErrorNat 22 11)).




(*functia aeval pt expresii aritmetice*)
Fixpoint aeval_fun (a : AExp) (env : Env) : ErrorNat :=
  match a with
  | avar v => match (env v) with
                | res_nat n => n
                | _ => error_nat
                end
  | anum v => v
  | aplus a1 a2 => (plus_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | amul a1 a2 => (mul_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | asub a1 a2 => (sub_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | adiv a1 a2 => (div_ErrorNat  (aeval_fun a1 env) (aeval_fun a2 env))
  | amod a1 a2 => (mod_ErrorNat (aeval_fun a1 env) (aeval_fun a2 env))
  | alung S1 => (lung_ErrorNat (env S1))
  end.


Compute aeval_fun ( StringLen ("asfasda") +' 123 ) env.

Compute aeval_fun ("var" +' 3) (update env "var" (res_nat 23)).








(*expresii boolene*)
Inductive BExp :=
  | berror
  | btrue
  | bfalse
  | bvar: string -> BExp (*variabile de tipul bool*)
  | blt : AExp -> AExp -> BExp
  | bgt : AExp -> AExp -> BExp
  | bnot : BExp -> BExp
  | band : BExp -> BExp -> BExp
  | bor : BExp -> BExp -> BExp
  | bstring : string -> string -> BExp.

(*notations for boolean operations*)
Notation "A <' B" := (blt A B) (at level 70).
Notation "A >' B" := (bgt A B) (at level 70).
Notation "!' A" := (bnot A)(at level 51, left associativity).
Notation "A &&' B" := (band A B)(at level 52, left associativity).
Notation "A ||' B" := (bor A B)(at level 53, left associativity).
Notation "'StringCompare' ( A , B )" := (bstring A B) (at level 50).

(*metode de calcul pentru operatii cu erori*)
Definition lt_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.ltb v1 v2)
    end.

Definition gt_ErrorBool (n1 n2 : ErrorNat) : ErrorBool :=
  match n1, n2 with
    | error_nat, _ => error_bool
    | _, error_nat => error_bool
    | num v1, num v2 => boolean (Nat.ltb v2 v1)
    end.

Definition not_ErrorBool (n :ErrorBool) : ErrorBool :=
  match n with
    | error_bool => error_bool
    | boolean v => boolean (negb v)
    end.

Definition and_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (andb v1 v2)
    end.

Definition or_ErrorBool (n1 n2 : ErrorBool) : ErrorBool :=
  match n1, n2 with
    | error_bool, _ => error_bool
    | _, error_bool => error_bool
    | boolean v1, boolean v2 => boolean (orb v1 v2)
    end.

Definition res_ErrorBool (r1 r2 : Result) : ErrorBool :=
match r1,r2 with
| res_string s1, res_string s2 => eqb s1 s2
| _,_ => false
end.
 
Compute and_ErrorBool false true.
Compute res_ErrorBool (res_string "test") (res_string "tet").
Compute or_ErrorBool (lt_ErrorBool 1 2) (gt_ErrorBool 3 4).
Compute or_ErrorBool (and_ErrorBool true true) false.






(*functia beval pentru expresii boolene*)
Fixpoint beval_fun (a : BExp) (envnat : Env) : ErrorBool :=
  match a with
  | btrue => true
  | bfalse => false
  | berror => error_bool
  | bvar v => match (env v) with (* rezultatul variabilei trebuie sa fie de tip bool*)
                | res_bool n => n
                | _ => error_bool
                end
  | blt a1 a2 => (lt_ErrorBool (aeval_fun a1 envnat) (aeval_fun a2 envnat))
  | bgt a1 a2 => (gt_ErrorBool (aeval_fun a1 envnat) (aeval_fun a2 envnat))
  | bnot b1 => (not_ErrorBool (beval_fun b1 envnat))
  | band b1 b2 => (and_ErrorBool (beval_fun b1 envnat) (beval_fun b2 envnat))
  | bor b1 b2 => (or_ErrorBool (beval_fun b1 envnat) (beval_fun b2 envnat))
  | bstring s1 s2=> (res_ErrorBool (envnat s1) (envnat s2))
  end.

Compute beval_fun (5 <' 2) env .





(*statements*)
Inductive Stmt :=
  | nat_decl: string -> Stmt (*declaratie numere naturale*)
  | bool_decl: string  -> Stmt  (*declaratie variabile boolene*)
  | string_decl : string ->Stmt (*declaratie de stringuri*)
  | vect_decl : string -> nat ->nat->Stmt (*declaratie vectori*)
  | struct_decl : string ->Stmt -> Stmt (*declaratie structuri*)

  | nat_assign : string -> AExp -> Stmt  (*asignare variabile naturale*)
  | bool_assign : string -> BExp -> Stmt  (*asignare variabile boolene*)
  | string_assign : string -> string ->Stmt (*asignare stringuri*)
  | var_assign : string -> string ->Stmt  (* asignare intre 2 variabile*)

  | sequence : Stmt -> Stmt -> Stmt (*secventa de statmenturi*)
  | while : BExp -> Stmt -> Stmt (*while*)
  | ifthenelse : BExp -> Stmt -> Stmt -> Stmt (* if then else*)
  | ifthen : BExp -> Stmt -> Stmt (* if then*)
  | case : ErrorNat -> Stmt -> Stmt (* caz pentru switch case*)
  | switch_case : AExp -> Stmt -> Stmt (* switch case*)

  | String_Cpy : string -> string -> Stmt 
  | String_Cat : string -> string -> Stmt.

(*notations for statements*)
Notation "'iNat' X " := (nat_decl X)(at level 90). (*declaratie nat*)
Notation "'iBool' X " := (bool_decl X)(at level 90). (*declaratie bool*)
Notation "'iString' X " := (string_decl X) (at level 90).
Notation "'natVect' X [ n ] " := (vect_decl X n 1) (at level 90).
Notation "'boolVect' X [ n ] " := (vect_decl X n 2) (at level 90).
Notation "'stringVect' X [ n ] " := (vect_decl X n 3) (at level 90).
Notation "'Structure' X { S }" := (struct_decl X S) (at level 90).

Notation "'Case' (' A ) {' S }" := (case A S) (at level 95).
Notation "'Switch' ( A ) : { S } " := (switch_case A S) ( at level 93).
Notation "X :n= A" := (nat_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "X :s= A" := (string_assign X A)(at level 90).
Notation "X :v= A" := (var_assign X A) (at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'CatTimp' ( B ) { S }" := (while B S) (at level 93).
Notation "'Daca' ( B ) 'atunci' { S } 'altfel' { S2 }" := (ifthenelse B S S2) (at level 93).
Notation "'Daca' ( B ) 'atunci' { S }" := (ifthen B S)( at level 93).
Notation "'Strcpy' ( S1 , S2 )":= (String_Cpy S1 S2) (at level 93).
Notation "'Strcat' ( S1 , S2 )":= (String_Cat S1 S2) (at level 93).


Compute iString "asdaddasa".
Compute iBool "true".
Compute Strcat ( "asda" , "asdader" ).

Definition to_char (n: nat) : string :=
 match n with
  | 0 =>"0"
  | 1 =>"1"
  | 2 =>"2"
  | 3 =>"3"
  | 4 =>"4"
  | 5 =>"5"
  | 6 =>"6"
  | 7 =>"7"
  | 8 =>"8"
  | 9 =>"9"
  | _ =>"0"

 end.
 
(*valoarea default in functie de tip*)
Definition res_check (n: nat) : Result :=
match n with
 | 1 => res_nat 0 
 | 2 => res_bool true
 | 3 => res_string "" 
 | _ => default
end.

Definition decl_check (s: Stmt) : nat :=
match s with
 | nat_decl a => 1
 | bool_decl a=> 2
 | string_decl a => 3
 | _ => 0
end.



Definition vect (env : Env) (s : string) (r: Result) : Env :=
  update env s r.




Definition vect_concat (s1 :string) (n:nat) : string :=
 StringConc (StringConc (StringConc s1 "[") (to_char n)) "]".
Fixpoint decl_vect (env : Env) (s : string) (n tip: nat) : Env :=
 match n with
  | 0 => env
  | S n'=> decl_vect (update (update env (vect_concat s n') default) (vect_concat s n') (res_check tip) ) s n' tip
 end.



(*tipul de date struct*)
Definition struct_concat (s1 s2 :string) : string :=
 StringConc (StringConc s1 ".") s2.

Compute struct_concat "x" "y".
Compute vect_concat "x" 5.

Compute (update env (struct_concat "s" "x") default) "s.x".
Compute (update (update env (struct_concat "s" "x") default) (struct_concat "s" "x") (res_nat 0)) "s.x" .

Fixpoint decl_struct ( env : Env) (s: string) (a : Stmt) : Env :=
match a with
 | sequence b c =>if(Nat.ltb 0 (decl_check b))
                  then match b with
                       | nat_decl x => decl_struct (update (update env (struct_concat s x) default) (struct_concat s x) (res_nat 0) ) s c
                       | bool_decl x => decl_struct (update (update env (struct_concat s x) default) (struct_concat s x) (res_bool true) ) s c
                       | string_decl x => decl_struct (update (update env (struct_concat s x) default) (struct_concat s x) (res_string "") ) s c
                       | _ => env
                       end
                  else env
 |nat_decl x => update (update env (struct_concat s x) default) (struct_concat s x) (res_nat 0)
 | bool_decl x => update (update env (struct_concat s x) default) (struct_concat s x) (res_bool true) 
 | string_decl x => update (update env (struct_concat s x) default) (struct_concat s x) (res_string "")
 | _ => env
end.


Compute (decl_struct env "coq" ( iString "language" ) ) "coq.language".

Definition Res_Conc (r1 r2 :Result) :Result :=
match r1,r2 with
| res_string s1, res_string s2 => res_string (StringConc s1 s2)
| _,_ => err_str
end.

(*statements eval*)
Fixpoint eval_fun (s : Stmt) (env : Env) (gas: nat) : Env :=
    match gas with
    | 0 => env
    | S gas' => match s with
                | nat_decl a => update (update env a default) a (res_nat 0)
                | bool_decl b => update (update env b default) b (res_bool true)
                | string_decl s => update env s default

                | nat_assign a aexp => update env a (res_nat (aeval_fun aexp env))
                | bool_assign b bexp => update env b (res_bool (beval_fun bexp env))
                | string_assign s str => update env s (res_string str)
                | var_assign s1 s2 =>if(check_eq_over_types (env s1) (env s2))
                                     then update env s1 (env s2)
                                     else env

                | vect_decl s n m=> decl_vect env s n m
                | struct_decl s n => decl_struct env s n

                | sequence S1 S2 => eval_fun S2 (eval_fun S1 env gas') gas' 
                
                | ifthen cond s' => 
                    match (beval_fun cond env) with
                    | error_bool => env
                    | boolean v => match v with
                                 | true => eval_fun s' env gas'
                                 | false => env
                                 end
                    end
                | ifthenelse cond S1 S2 => 
                    match (beval_fun cond env) with
                        | error_bool => env
                        | boolean v  => match v with
                                 | true => eval_fun S1 env gas'
                                 | false => eval_fun S2 env gas'
                                 end
                         end
                | while cond s' => 
                    match (beval_fun cond env) with
                        | error_bool => env
                        | boolean v => match v with
                                     | true => eval_fun (s' ;; (while cond s')) env gas'
                                     | false => env
                                     end
                        end
                | case n St =>eval_fun St env gas'
               
                | switch_case AE C =>
                                 match C with
                                         | case n St => if(ErrorNat_beq n (aeval_fun AE env))  
                                                       then eval_fun St env gas'
                                                        else env
                                          | sequence S1 S2 => match S1 with    
                                                              | case n St => if(ErrorNat_beq n (aeval_fun AE env))  
                                                                            then eval_fun St env gas'   
                                                                            else eval_fun (switch_case AE S2) env gas'
                                                               | _ => env
                                                                end
                                         | _ => env
                                 end
              
                 | String_Cpy S1 S2 => update env S1 (env S2) 
                 | String_Cat S1 S2 => update env S1 (Res_Conc (env S1) (env S2))               
                end
    end.


Definition ex1 :=
 iNat "x" ;;
 iNat "y" ;;
 iNat "z";;
 "x" :n= 12 ;;
 "y" :n= 13 ;;
 "z" :n= "x" +' "y".

Compute (eval_fun ex1 env 100) "z".


Definition ex2:=
 iNat "x";;
 "x" :n=12 ;;
 Daca ("x" <' 22 ) atunci { "x" :n= 23 }.

Compute (eval_fun ex2 env 100) "x".

Definition ex3 :=
iNat "x" ;;
iNat "y" ;;
"x" :n= 12 +' 13 ;;
Switch ("x" ) : {
Case ('25) {' "y" :n= 26} ;;
Case ('3) {' "y" :n= 3} ;;
Case ('15) {' "y" :n= 15}
}.

Compute (eval_fun ex3 env 100) "y". 




