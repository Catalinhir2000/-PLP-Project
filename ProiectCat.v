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
 
Compute res_ErrorBool (res_string "test") (res_string "tet").
Compute or_ErrorBool (lt_ErrorBool 1 2) (gt_ErrorBool 3 4).
Compute or_ErrorBool (and_ErrorBool true true) false.













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

Notation "'Case' ( A ) { S }" := (case A S) (at level 95).
Notation "'Switch' ( A ) : S " := (switch_case A S) ( at level 93).
Notation "X :n= A" := (nat_assign X A)(at level 90).
Notation "X :b= A" := (bool_assign X A)(at level 90).
Notation "X :s= A" := (string_assign X A)(at level 90).
Notation "X :v= A" := (var_assign X A) (at level 90).
Notation "S1 ;; S2" := (sequence S1 S2) (at level 93, right associativity).
Notation "'CatTimp' ( B ) { S }" := (while B S) (at level 93).
Notation "'Daca' ( B ) 'atunci' {' S } 'altfel' {' S2 }" := (ifthenelse B S S2) (at level 93).
Notation "'Daca' ( B ) 'atunci' {' S }" := (ifthen B S)( at level 93).
Notation "'Strcpy' ( S1 , S2 )":= (String_Cpy S1 S2) (at level 93).
Notation "'Strcat' ( S1 , S2 )":= (String_Cat S1 S2) (at level 93).

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




Definition struct_concat (s1 s2 :string) : string :=
 StringConc (StringConc s1 ".") s2.

Compute struct_concat "a" "m".
Compute vect_concat "x" 5.

Compute (update env (struct_concat "s" "x") default) "s.x".
Compute (update (update env (struct_concat "s" "x") default) (struct_concat "s" "x") (res_nat 0)) "s.x" .







