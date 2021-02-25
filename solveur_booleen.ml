(**
 *                              SOLVEUR BOOLEEN
 *
 *
 *  Ce programme développer en OCAML nous permet de résoudre un système
 *  d'équations booleenes, et cela en créant le système et en appelant la
 *  fonction "solveur_booleen" sur le systeme déclaré.
 *
 *
 * @author Mohand Lounis BENSEKHRI    11710457
 * @author Lounis LAOUAZI             11709378
 * @since Année universitaire: 2018 - 2019
 *)

(**
 *  Le type eb "expression booleene" contient une infinitée de variables, deux constantes
 *  (TRUE) et (FALSE), ainsi les quatre connecteurs (AND), (OR), (XOR) et (NOT).
 *)
type eb = V of int | TRUE | FALSE | AND of eb * eb | OR of eb * eb | XOR of eb * eb | NOT of eb ;;



(******************************************************************************)
(*                                 QUESTION 1                                 *)
(******************************************************************************)

(**
 *  Cette fonction permet de déterminer l'ensemble des variable d'une expression
 *  booleenne.
 *
 * @param e une expression booleene.
 * @return une liste des variables de e.
 *)
let rec ensVarEB e =
  match e with
    |V(x)  -> e::[]
    |TRUE  -> []
    |FALSE -> []
    |AND(x, y) -> (ensVarEB x) @ (ensVarEB y)
    |OR(x, y)  -> (ensVarEB x) @ (ensVarEB y)
    |XOR(x, y) -> (ensVarEB x) @ (ensVarEB y)
    |NOT(x)    -> (ensVarEB x)
    ;;


(**
 *  Cette fonction permet de déterminer si un elt appartient à une liste.
 *
 * @param l la liste dans laquelle chercher.
 * @param v l'element à chercher.
 * @return true si trouver, false sinon.
 *)
let rec appartient l v =
  match (l,v) with
    |([], V(x)) ->  false
    |([], _)    ->  false
    |(a::b, V(x)) ->  if (a = V(x))
                      then true
                      else (appartient b v)
    |(a::b, _)    ->  false
    ;;


(**
 *  Cette fonction permet de supprimer un elt repétée dans une liste.
 *  le but de cette fonction est d'enlver les répition dans la liste fournise
 *  par la fonction "ensVarEB"
 *
 * @param l une liste d'expressions booleenes avec répetitions.
 * @return l sans répetitions.
 *)
let rec supRep l =
  match l with
  |[]   -> []
  |x::y ->  if ((appartient y x) == false)
            then [x] @ (supRep y)
            else (supRep y)
  ;;


(**           ***
 *  Cette fonction permet de déterminer l'ensembles des variables d'un système
 *  d'expressions, qui est caractériser par une liste de couple d'expressions
 *  booleenes.
 *  Si le systeme est vide on déclenche une exception.
 *
 * @param l la liste de eb * eb.
 * @return une liste des variables du systeme list eb.
 *)
let rec variableSysExp l =
  match l with
  |[] -> failwith "Le systeme est vide !"
  |(x1, x2)::q -> let l1 = ensVarEB (x1) in
                  let l2 = ensVarEB (x2) in
                  let l3 = supRep (l1@l2) in
                  if (List.length q != 0)
                  then supRep(l3@variableSysExp q)
                  else l3
  ;;



(******************************************************************************)
(*                                 QUESTION 2                                 *)
(******************************************************************************)

(**
 *  Cette fonction permet de dupliquer la tête d'une liste et ajoute pour la
 *  1ère TRUE, la seconde FALSE, et s'auto appel sur le reste et cela jusqu'a
 *  la fin de la liste. Si la liste est vide, elle renvoie une liste de listes.
 *
 * @param l la liste.
 *)
let rec ajoutFalseTrueT l =
  match l with
    |[] -> [[]]
    |x::[] -> [x @ [TRUE]] @ [x @ [FALSE]]
    |x::q  -> (x @ [TRUE])::(x @ [FALSE])::(ajoutFalseTrueT q)
    ;;


(**           ***
 *  Cette fonction permet de générer une table de vérité et cela en lui passant
 *  en param le nb de variable "n", cela pour générer 2^n cas possible pour les
 *  valeur de vérité pour les n variables.
 *
 * @param n le nombre de variables.
 *)
let rec tableDeVerite n =
  match n with
    |0 -> []
    |1 -> [[TRUE]; [FALSE]]
    |_ -> let aux = tableDeVerite (n-1) in ajoutFalseTrueT aux
    ;;


(**
 *  Cette fonction permet de mettre chaque deux element du même indice de deux
 *  liste dans un couple qui sera ajouter à la liste result, si l'une des deux
 *  listes est vide on renvoie la liste vide.
 *
 * @param l1 la première liste
 * @param l2 la deuxième liste
 * @return la liste des couples formés, ou la liste vide si l1 ou l2 est vide.
 *)
let rec couple l1 l2 =
  match (l1,l2) with
    |([], l2) -> []
    |(l1, []) -> []
    |(x1::q1, x2::q2) -> (x1, x2)::(couple q1 q2)
    ;;


(**           ***
 *  Cette fonction est la fonction final en effet elle permet de générer tous
 *  les environnements possibles qui sont une liste de couple
 *  (variable, valeur de véritée).
 *
 * @param l1 la table de vérité.
 * @param l2 liste de variables.
 *)
let rec creatEnvironment l1 l2 =
  match l1 with
    |[] -> [[]]
    |x::[] ->  [(couple l2 x)]
    |x::q  ->  couple l2 x :: (creatEnvironment q l2)
    ;;



(******************************************************************************)
(*                                 QUESTION 3                                 *)
(******************************************************************************)

(**
 *  Cette fonction permet de tester une expression booleene et la simplifier en
 *  une valeur de vérité ou variable et cela en définissant les différents
 *  connecteurs du type eb.
 *
 * @param e l'expresion booleene.
 * @return TRUE, ou FALSE.
 *)
let rec simplificationEquation e =
  match e with
    |V(x)  -> V(x)
    |TRUE  -> TRUE
    |FALSE -> FALSE
    |AND(x, y) -> if(x = TRUE)
                  then simplificationEquation y
                  else  if(x = FALSE)
                        then FALSE
                        else simplificationEquation(AND(simplificationEquation x, simplificationEquation y))
    |OR(x, y) -> if(x = FALSE)
                 then simplificationEquation y
                 else if (x = TRUE)
                      then TRUE
                      else simplificationEquation(OR(simplificationEquation x, simplificationEquation y))
    |XOR(x, y) -> if(x = FALSE)
                  then simplificationEquation y
                  else if (x = TRUE)
                       then simplificationEquation(NOT y)
                       else simplificationEquation(XOR(simplificationEquation x, simplificationEquation y))
    |NOT(x) -> if(x = FALSE)
               then TRUE
               else if(x = TRUE)
                    then FALSE
                    else simplificationEquation(NOT(simplificationEquation x))
    ;;


(**
 *  Cette fonction permet de convertir chaque variable à sa valeur.
 *
 * @param env un environnement.
 * @param e une expression booleene.
 * @return la valeur de la valeur booleene
 *)
let rec convVarVal env e =
  match (env, e) with
    |([], x) -> x
    |((a,b)::q, V(x)) ->  if (a = V(x))
                          then b
                          else convVarVal q (V(x))
    |(env, TRUE)  -> TRUE
    |(env, FALSE) -> FALSE
    |((a, b)::q, AND(x, y)) -> AND(convVarVal env x, convVarVal env y)
    |((a, b)::q, OR(x, y))  -> OR(convVarVal env x, convVarVal env y)
    |((a, b)::q, XOR(x, y)) -> XOR(convVarVal env x, convVarVal env y)
    |((a, b)::q, NOT(x))    -> NOT(convVarVal env x)
    ;;


(**
 *  Cette fonction permet de tester la compatibilité d'un environnement dans un
 *  systeme d'equations booleenes qui est une liste de couple de eb.
 *  Et cela en testant chaque equation du systeme.
 *
 * @param env l'environnement.
 * @param syseq le systeme d'equations booleene.
 * @return l'environnement qui vérifie le systeme
 *)
let rec testMiniEnvSurSys env syseq =
  match syseq with
    |[] -> env
    |(x, y)::q -> if((simplificationEquation (convVarVal env x)) = (simplificationEquation (convVarVal env y)))
                  then testMiniEnvSurSys env q
                  else []
    ;;


(**           ***
 *  Cette fonction est la fonction final en effet elle permet de tester la
 *  compatibilitée tous les environnements généré passé en arg dans toutes
 *  les équations du systeme.
 *
 * @param listEnv tous les environnements possibles.
 * @param syseq le systeme d'equations booleene.
 * @return la liste de tous les environnements qui vérifie le systeme.
 *)
let rec solSysEq listEnv syseq =
  match listEnv with
    |[] -> []
    |x::q -> if((testMiniEnvSurSys x syseq) = [])
             then solSysEq q syseq
             else (testMiniEnvSurSys x syseq)::(solSysEq q syseq)
    ;;



(******************************************************************************)
(*                                   MAIN                                     *)
(******************************************************************************)

(**
 *  Cette fonction permet de mettre toutes les fonctions qui permettent de
 *  résoudre un solveur booleen dans une seule fonction et cela pour simplifier
 *  l'utilisation du programme.
 *  Cette fonction remplace:
 *    let variablesSys = variableSysExp sysExp ;;
 *    let nbVariables = List.length variablesSys ;;
 *    let tableauDeVerite = tableDeVerite nbVariables ;;
 *    let environnement = creatEnvironment tableauDeVerite variablesSys ;;
 *
 * @param syseq le systeme d'expresion booleenes.
 * @return la solutions de syseq.
 *)
let solveur_booleen syseq =
  solSysEq (creatEnvironment (tableDeVerite (List.length (variableSysExp syseq))) (variableSysExp syseq)) syseq ;;



(** EXEMPLE D'EXECUTION DU PROGRAMME *)
let sysExp = [(OR(V(1), V(2)), TRUE); (XOR(V(1), V(3)), V(2)); (NOT(AND(V(1), (AND(V(2), V(3))))), TRUE)] ;;
print_endline "Demonstration du resultat pour la question 01: " ;;
let question1 = variableSysExp sysExp ;;
let nbVariables = List.length question1 ;;
let tableauDeVerite = tableDeVerite nbVariables ;;
print_endline "Demonstration du resultat pour la question 02: " ;;
let question2 = creatEnvironment tableauDeVerite question1;;
print_endline "Demonstration du resultat pour la question 03: " ;;
let question3 = solSysEq question2 sysExp ;;


print_endline "Demonstration en utilisant la fonction principale " ;;
let solutions_systeme_equations = solveur_booleen sysExp ;;



(******************************************************************************)
(*                              JEUX D'ESSAIS                                 *)
(******************************************************************************)

(**
 *  Premier essaie:
 *  3 variables et 3 equations.
 *  cela nous donne une seule solution qui est:
 *  [[(V 3, FALSE); (V 1, TRUE); (V 2, TRUE)]]
 *)
let essaie1 = [(OR(V(1), V(3))), TRUE; (AND(V(2), (NOT(V(3))))), TRUE; (NOT(XOR(V(1), V(2)))), TRUE] ;;
let sol_essaie1 = solveur_booleen essaie1 ;;


(**
 *  Second essaie:
 *  4 variables et 4 equations.
 *  cela nous donne deux solution qui sont:
 *  [(OR (V 1, NOT (V 2)), TRUE); (XOR (V 3, V 4), TRUE); (OR (V 4, V 1), TRUE); (OR (V 2, NOT (V 1)), TRUE)]
 *)
let essaie2 = [(OR(V(1), NOT(V(2))), TRUE); (XOR(V(3),V(4)), TRUE); (OR(V(4),V(1)), TRUE); (OR(V(2),NOT(V(1))), TRUE)] ;;
let sol_essaie2 = solveur_booleen essaie2 ;;


(**
 *  Troisième essaie:
 *  3 variables et 1 seule equation.
 *  cela nous donne une 8 solutions comme tous les cas sont vérifié on peut dire
 *  que l'équation est une tautologie. ces solution est toute la table de vérité.
 *    [[(V 2, TRUE); (V 1, TRUE); (V 3, TRUE)];
 *    [(V 2, TRUE); (V 1, TRUE); (V 3, FALSE)];
 *    [(V 2, TRUE); (V 1, FALSE); (V 3, TRUE)];
 *    [(V 2, TRUE); (V 1, FALSE); (V 3, FALSE)];
 *    [(V 2, FALSE); (V 1, TRUE); (V 3, TRUE)];
 *    [(V 2, FALSE); (V 1, TRUE); (V 3, FALSE)];
 *    [(V 2, FALSE); (V 1, FALSE); (V 3, TRUE)];
 *    [(V 2, FALSE); (V 1, FALSE); (V 3, FALSE)]]
 *)
let essaie3 = [(OR(V(1), (AND(V(2), V(3))))), (AND((OR(V(1), V(2))), (OR(V(1), V(3))) ) )] ;;
let sol_essaie3 = solveur_booleen essaie3 ;;


(**
 *  Quatrième essaie:
 *  3 variables et 4 equations.
 *  cela nous donne une seule solution qui est:
 *  [[(V 2, FALSE); (V 4, FALSE); (V 3, TRUE); (V 1, TRUE); (V 5, TRUE)]]
 *)
let essaie4 = [(XOR(V(1), V(2)), TRUE); (XOR(V(3),V(4)), TRUE); (AND(V(1),V(3)), TRUE); (NOT(AND(V(1),NOT(V(5)))), TRUE)] ;;
let sol_essaie4 = solveur_booleen essaie4 ;;


(**
 *  Cinquième essaie:
 *  5 variables et 4 equations.
 *  cela nous donne aucune solution :
 *  []
 *)
let essaie5 = [(AND(V(1), V(3)), TRUE); (OR(V(3),NOT(V(4))), TRUE); (XOR(V(1),V(3)), TRUE); (NOT(OR(V(1),NOT(V(5)))), TRUE)] ;;
let sol_essaie5 = solveur_booleen essaie5 ;;


(**
 *  Sixième essaie:
 *  7 variables et 5 equations.
 *  cela nous donne une 8 solutions qui sont:
 *  [[(V 4, TRUE); (V 3, TRUE); (V 5, TRUE); (V 1, FALSE); (V 6, TRUE); (V 7, TRUE)];
 *  [(V 4, TRUE); (V 3, TRUE); (V 5, TRUE); (V 1, FALSE); (V 6, TRUE); (V 7, FALSE)];
 *  [(V 4, TRUE); (V 3, TRUE); (V 5, TRUE); (V 1, FALSE); (V 6, FALSE);(V 7, TRUE)];
 *  [(V 4, TRUE); (V 3, TRUE); (V 5, TRUE); (V 1, FALSE); (V 6, FALSE); (V 7, FALSE)];
 *  [(V 4, FALSE); (V 3, TRUE); (V 5, TRUE); (V 1, FALSE); (V 6, TRUE); (V 7, TRUE)];
 *  [(V 4, FALSE); (V 3, TRUE); (V 5, TRUE); (V 1, FALSE); (V 6, TRUE); (V 7, FALSE)];
 *  [(V 4, FALSE); (V 3, TRUE); (V 5, TRUE); (V 1, FALSE); (V 6, FALSE); (V 7, TRUE)];
 *  [(V 4, FALSE); (V 3, TRUE); (V 5, TRUE); (V 1, FALSE); (V 6, FALSE); (V 7, FALSE)]]
 *)
let essaie6 = [(OR(V(1), V(3)), TRUE); (OR(V(3),NOT(V(4))), TRUE); (OR(V(1),V(3)), TRUE); (NOT(OR(V(1),NOT(V(5)))), TRUE); (NOT(AND(V(1), (AND(V(6), V(7))))), TRUE)] ;;
let sol_essaie6 = solveur_booleen essaie6 ;;
(** FIN ESSAIE *)

(** A VOUS DE JOUER ! *)
print_endline "A vous de jouer creez votre systeme et appelez la fonction solveur_booleen sur votre systeme !" ;;
