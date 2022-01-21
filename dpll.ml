open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []



(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"



(********************************************************************)
(***********Exemples***********)    
(* ensembles de clauses de test *)

let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]



(********************************************************************)
(***********Fonction Simplifie***********)

(* simplI : int -> int list list -> int list list 
   supprime les clauses contenant le litteral i*)
let rec simplI i clauses = 
  let fonctionFilter elem =
    if elem = i then
      None
    else 
      Some elem
  in

  match clauses with
  | [] -> []
  | [ [] ] -> [ [] ]
  | []::l -> [] :: simplI i l
  | [x] ->
      let res = List.rev(filter_map fonctionFilter x)  in
      if res = x then
        [x]
      else 
        []
  | x::l ->
      let res = List.rev(filter_map fonctionFilter x) in
      if res = x then
        res::simplI i l    
      else 
        simplI i l


(* simplNotI : int -> int list list -> int list list 
   supprime li litteral notI des clauses le contenant *)
let rec simplNotI notI clauses = 

  let fonctionFilter elem =
    if elem = notI then
      None
    else 
      Some elem
  in

  match clauses with
  | [] -> []
  | [ [] ] -> [ [] ]
  | []::l -> []::simplNotI notI l
  | [x] ->
    [List.rev(filter_map fonctionFilter x)]
  | x::l ->
      let res = List.rev(filter_map fonctionFilter x) in
      res::simplNotI notI l    


(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral i à vrai *)
let simplifie i clauses =

  let clausesWithoutI = simplI i clauses in 
  simplNotI (-i) clausesWithoutI
  
  


(********************************************************************)
(***********Solveur Split***********)

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* un clause vide est insatisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche

(* tests *)
(* let () = print_modele (solveur_split systeme []) *)
(* let () = print_modele (solveur_split coloriage []) *)




(********************************************************************)
(***********Fonction Unitaire***********)    

(* isUnitaire : int list -> boolean
    - si `clauses' contient un litteral alors retourne true ;
    - sinon, retourne false *)
let isUnitaire clause =
  match clause with
  | [] -> false
  | [x] -> true
  | x::l -> false


(* unitaire : int list list -> int
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
    - sinon, retourne une erreur "Not Found" *)
let rec unitaire clauses =
  match clauses with
  | [] -> raise Not_found
  | [x] -> 
    if (isUnitaire x) then
      List.hd x
    else 
      raise Not_found
  | x::l ->
    if (isUnitaire x) then
      List.hd x
    else 
      unitaire l




(********************************************************************)
(***********Fonction Pur***********)   

(* parcoursFin : int list -> int list -> int
    - si `listeParcourus' contient un littéral pur, retourne
      ce littéral ;
    - sinon, retourne une erreur "Not Found" *)
let rec parcoursFin listParcourus liste2 = 
  match liste2 with
  | [] -> raise Not_found
  | [x] -> 
    if List.mem (-x) listParcourus then
      raise Not_found
    else 
      x
  | x::l ->
    if List.mem (-x) listParcourus then
      parcoursFin listParcourus l
    else 
      x


(* pur : int list list -> int
    - parcours clauses pour faire une liste des variables présentes
    - lance ParcoursFin quand clauses a finit d'etre parcourue
    - retourne le resultat obtenu*)
let pur clauses =

  let rec parcoursClauses clauses parcourus=
    match clauses with
    | [] -> parcoursFin parcourus parcourus
    | [ [] ] -> parcoursFin parcourus parcourus

    | []::l -> parcoursClauses l parcourus

    | [ [x] ] ->
      if List.mem x parcourus  then
        parcoursFin parcourus parcourus
      else 
        parcoursFin (x::parcourus) (x::parcourus)

    | [ x::l ] -> 
      if List.mem x parcourus then
        parcoursClauses [l] parcourus
      else 
        parcoursClauses [l] (x::parcourus)

    | (x::l)::ll  -> 
      if List.mem x parcourus then
        parcoursClauses ( l::ll) parcourus
      else 
        parcoursClauses ( l::ll)  (x::parcourus)

  in parcoursClauses clauses []




(********************************************************************)
(***********Solveur DPLL Recursif***********)

(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =

  (* clauses = vide ? -> interpretation*)
  if clauses = [] then
    Some interpretation

  (* clauses contient [] ? -> None *)
  else if  mem [] clauses then 
    None 
  
  else
      (* unitaire ? -> simplification de clauses par l'unitaire, et ajout de l'unitaire à interpretation *)
      try 
      let uni = unitaire clauses in
      solveur_dpll_rec (simplifie uni clauses) (uni::interpretation)
      with 
        Not_found -> 
          (* pur ? -> simplification de clauses par le litteral pur, et ajout du litteral pur à interpretation *)
          try 
            let pure = pur clauses in
            solveur_dpll_rec (simplifie pure clauses) (pure::interpretation)
          with 
            Not_found -> 
              (* prendre la premiere variable qui apparait dans clauses *)
              (* -> simplification de clauses par la variable, et ajout de la variable à interpretation *)
              let var  = hd (hd clauses) in
              solveur_dpll_rec (simplifie var clauses) (var::interpretation)

    

(* tests *)
(* let () = print_modele (solveur_dpll_rec exemple_7_2 []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)
(* let () = print_modele (solveur_dpll_rec systeme []) *)

 let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses []) 
