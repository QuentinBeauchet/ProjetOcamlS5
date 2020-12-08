#load "graphics.cma";;
#load "unix.cma";;
#directory "+threads";;
#load "threads.cma";;
open Graphics;;
Graphics.open_graph " 600x600";;
Random.self_init ();;

(*-----------------------------Variables Globales-----------------------------*)
let largeur=20;;
let hauteur=20;;
let largeur_case=20;;
let bordX=50;;
let bordY=550;;

(*-----------------------------Definition UnionFind-----------------------------*)
module type Unionfind =sig 
type arbre 
type unionfind 
val create : int -> unionfind
val find : unionfind -> int -> int 
val union : unionfind -> int -> int -> unit 
end 

(*-----------------------------Fonctions UnionFind-----------------------------*)
module UF :Unionfind = struct
type arbre =
| Racine
| Fils of int
type unionfind = arbre array
let create n  =
Array.make n Racine

let rec find uf  i =
match uf.(i) with
| Fils j ->
let racine = find uf j in
uf.(i) <- Fils racine ; racine
| Racine -> i    (* la racine est le représentant *)
let union uf  i  j  =
let racineIndex = find uf i in
(* choix arbitraire de préférer la racine de i,
on devrait préférer celle de l'arbre le plus petit pour "écraser" la forêt.
*)
uf.(racineIndex) <- Fils j
end 

(*-----------------------------Fonctions Labyrinthe-----------------------------*)
let cases_adjacentes (l: int) (h:int) ((d,x,y): int*int*int )  : int*int =
(x*l+y , x*l+y+1+d*(l-1));;
let mur_au_hasard (g:int) (z:int) : int*int*int   = (* renvoie un triplet (d, x, y) *)
let n = Random.int ((g-1) * z + g * (z-1)) in
if n < (g-1) * z then
(0, n mod (g-1), n/(g-1))
else
let n2 = n - (g-1) * z in
(1, n2 mod g, n2/g);;

let initmur_present l h= (* tous les murs sont initialisés à true *)
let ver = Array.init (l-1) (fun _ -> (Array.make h true )) in
let hor = Array.init l (fun _ -> (Array.make (h-1) true )) in
[|hor;ver|];;

let generate_lab (l:int) ( h:int ) : bool array array array   =
(* tous les murs sont initialise a true *)
let mur_present = initmur_present l h in

(*Allocation de l'UnionFind*)
let tab = UF.create (l*h) in 
let iter = ref 1 in (*nombre des mur retirés*)
while !iter < l*h do
let (d,x,y) = mur_au_hasard l h in
let (a,b)= cases_adjacentes l h (d,y,x) in
if UF.find tab a = UF.find tab b then
iter := !iter
else begin
if mur_present.(d).(y).(x)=false then
iter:=!iter
else
UF.union tab a b;
mur_present.(d).(y).(x)<-false;
iter:=!iter+1;
end;
done;
mur_present;;

(*-----------------------------Fonctions Graphique-----------------------------*)
let trace_pourtour upleftx uplefty taille_case l h =
(*HAUT*)
Graphics.moveto upleftx uplefty;
Graphics.lineto (upleftx+taille_case*l) uplefty;
(*BAS*)
Graphics.moveto upleftx (uplefty-taille_case*h);
Graphics.lineto (upleftx+taille_case*l) (uplefty-taille_case*h);
(*GAUCHE*)
Graphics.moveto upleftx (uplefty-taille_case);
Graphics.lineto upleftx (uplefty-taille_case*h);
(*DROITE*)
Graphics.moveto (upleftx+taille_case*l) uplefty;
Graphics.lineto (upleftx+taille_case*l) (uplefty-taille_case*(h-1));;

let trace_mur upleftx uplefty taille_case (d,x,y)=
if d==0 then begin (*mur vertical *)
Graphics.moveto (upleftx+taille_case*(y+1)) (uplefty-taille_case*x);
Graphics.lineto (upleftx+taille_case*(y+1)) (uplefty-taille_case*(x+1));
end
else begin (* mur horizontal *)
Graphics.moveto (upleftx+taille_case*y) (uplefty-taille_case*(x+1));
Graphics.lineto (upleftx+taille_case*(y+1)) (uplefty-taille_case*(x+1));
end;;

let trace_lab upleftx uplefty taille_case l h mur_present=
trace_pourtour upleftx uplefty taille_case l h;
for a=0 to ((Array.length mur_present)-1) do
for b=0 to ((Array.length mur_present.(a))-1) do
for c=0 to ((Array.length mur_present.(a).(b))-1) do
if mur_present.(a).(b).(c)==true then (*mur present *)
trace_mur upleftx uplefty taille_case (a,b,c)
else begin
(*Rien dessiner*)
Graphics.moveto 0 0;
Graphics.lineto 0 0;
end
done;
done;
done;;

(*-----------------------------Entity-----------------------------*)
let case_pacman = ref 0;;
let couleur_pacman = (rgb 0 0 255);;

let case_fantome= ref (largeur-1);;
let couleur_fantome = (rgb 255 0 0);;

(*Affiche pacman/le fantome*)
let afficheEntity (entity,entityColor)=
Graphics.set_color entityColor;
let posX=bordX+(!entity mod largeur)*largeur_case + largeur_case/2 in
let posY=bordY -(!entity/largeur)*largeur_case - largeur_case/2 in
Graphics.fill_circle posX posY (largeur_case/2 -1);;

(*Supprime le pacman/fantome precedent*)
let supEntity (entity,entityColor)=
afficheEntity (entity,(rgb 255 255 255));;

(*Mise a jour de pacman*)
let deplacementEntity (entity,entityColor) x=
supEntity (entity,entityColor);
entity:= !entity + x;
afficheEntity (entity,entityColor);;

(*-----------------------------Pacman-----------------------------*)

(*L'inverse de la fonction cases_adjacentes, renvoit le triplet (d,x,y) a partir de deux cases (a,b)*)
let inv_CA (a,b)=
if (a-b)==1 || (a-b)== -1 then
(0,a/largeur,(b mod largeur)-1)
else
(1,a/largeur,b mod largeur);;

(*Renvoit un boolean si pacman peut se deplacer de la case A a la case B*)
let isDeplacementPossible entity tableau_mur deplacement=
(*Vers le haut*)
if deplacement==(-largeur) then begin
if !entity<largeur then
false
else begin
let (d,x,y) = inv_CA (!entity+deplacement,!entity) in
if tableau_mur.(d).(x).(y)==false then
true
else false
end
end
(*Vers le bas*)
else if deplacement==largeur then begin
if !entity>=(largeur*(hauteur-1)) then
false
else begin
let (d,x,y) = inv_CA (!entity,!entity+deplacement) in
if tableau_mur.(d).(x).(y)==false then
true
else false
end
end
(*Vers la gauche*)
else if deplacement==(-1) then begin
if !entity mod largeur==0 then
false
else begin
let (d,x,y) = inv_CA (!entity+deplacement,!entity) in
if tableau_mur.(d).(x).(y)==false then
true
else false
end
end
(*Vers la droite*)
else begin
if (!entity+1) mod largeur==0 then
false
else begin
let (d,x,y) = inv_CA (!entity,!entity+deplacement) in
if tableau_mur.(d).(x).(y)==false then
true
else false
end
end

(*Lis les touches du clavier*)
let mouvement tableau_mur=
let lettre=read_key() in
(*HAUT*)
if lettre=='z' then begin
let move = -largeur in
if (isDeplacementPossible case_pacman tableau_mur move)==true then
deplacementEntity (case_pacman,couleur_pacman) move;
end
(*GAUCHE*)
else if lettre=='q' then begin
let move = -1 in
if (isDeplacementPossible case_pacman tableau_mur move)==true then
deplacementEntity (case_pacman,couleur_pacman) move;
end
(*BAS*)
else if lettre=='s' then begin
let move = largeur in
if (isDeplacementPossible case_pacman tableau_mur move)==true then
deplacementEntity (case_pacman,couleur_pacman) move;
end
(*DROITE*)
else if lettre=='d' then begin
let move = 1 in
if (isDeplacementPossible case_pacman tableau_mur move)==true then
deplacementEntity (case_pacman,couleur_pacman) move;
end
else ();
if !case_pacman= !case_fantome then begin
Printf.printf "%s\n" "PERDU !!!";
exit 0;
end;;

(*Affiche le labyrinth et la position de depart de pacman*)
let initialisation tableau_mur=
trace_lab bordX bordY largeur_case largeur hauteur tableau_mur;
Graphics.set_color couleur_pacman;
afficheEntity (case_pacman,couleur_pacman);;

(*-----------------------------Chemin du fantome a pacman-----------------------------*)

(*Pour chaque case Tableau de boolean [|HAUT;BAS;GAUCHE;DROITE|]*)
let voisins tableau_mur=
let direction=[|false;false;false;false|] in
let tableau_direction=Array.init (largeur*hauteur) (fun i -> Array.copy direction) in
let pos=ref 0 in
for i=0 to (largeur*hauteur -1) do
pos:=i;
(*HAUT*)
if not(i<largeur) then begin
tableau_direction.(i).(0)<-isDeplacementPossible pos tableau_mur (-largeur);
end;
(*BAS*)
if not(i>=(largeur*(hauteur-1))) then begin
tableau_direction.(i).(1)<-isDeplacementPossible pos tableau_mur largeur;
end;
(*GAUCHE*)
if not((i mod largeur)==0) then begin
tableau_direction.(i).(2)<-isDeplacementPossible pos tableau_mur (-1);
end;
(*DROITE*)
if not((i+1) mod largeur==0) then begin
tableau_direction.(i).(3)<-isDeplacementPossible pos tableau_mur 1;
end;
done;
tableau_direction;;

(*Tableau [|N;S;E;W|] pour chaque case, chaque index vaut soit la case adjacnetes s'il n'y a pas de mur ou elle même sinon*)
let num_voisins tableau_voisins=
let t=Array.init (largeur*hauteur) (fun x -> Array.make 4 0) in
for i=0 to (Array.length t -1) do begin
(*Sauf premiere ligne*)
if tableau_voisins.(i).(0)=false then
t.(i).(0)<-i
else
t.(i).(0)<-(i-largeur);
(*Sauf derniere ligne*)
if tableau_voisins.(i).(1)=false then
t.(i).(1)<-i
else
t.(i).(1)<-(i+largeur);
(*Sauf premiere colone*)
if tableau_voisins.(i).(2)=false then
t.(i).(2)<-i
else
t.(i).(2)<-(i-1);
(*Sauf derniere colone*)
if tableau_voisins.(i).(3)=false then
t.(i).(3)<-i
else
t.(i).(3)<-(i+1)
end
done;
t;;

(*Sens horaire N->W->S->E->N *)
let rotate i=
if i=0 then
3
else if i=1 then
2
else if i=2 then
0
else 1;;

(*Algorithme Left Hand Rule pour resoudre le labyrinthe*)
let trajet src dest tableau=
let chemin=Array.init 10000 (fun x -> 0) in
let rec fonction src dest dir index tab=
chemin.(index)<-src;
if src=dest then
true
else begin
if tab.(src).(dir)!=src then begin
fonction tab.(src).(dir) dest (rotate(rotate(rotate dir))) (index+1) tab
end
else if tab.(src).(rotate dir)!=src then begin
fonction tab.(src).(rotate dir) dest dir (index+1) tab
end
else begin
fonction tab.(src).(dir) dest (rotate dir) (index+1) tab;
end
end
in
if fonction src dest 0 0 tableau then
chemin
else
[|src|];;

(*Supprime les parties inutiles du chemin ex: [|...;13;19;18;17;18;19;15...|] -> [|...;13;19;15;...|]  *)
let saute_noeud index t=
let acc=ref 0 in
for i=0 to (Array.length t-1) do
if t.(index)=t.(i) then
acc:=i
else ()
done;
(*Coupe le tableau entre index et !acc*)
if index!= !acc then begin
let v1=Array.sub t 0 index in
let v2=Array.sub t !acc (Array.length t -(!acc)) in
Array.append v1 v2;
end
else t;;

(*Chemin le plus court quand il y a les doublons on appelle saute noeud pour couper entre les doublons et il enleve les 0 *)
let sup t=
let m=ref t in
let i=ref 0 in
m:=saute_noeud !i t;
while !i<(Array.length !m-1)do
i:=!i+1;
m:=saute_noeud !i !m;
done;
!m;;

(*Determine le chemin du fantome*)
let chemin src dst tableau_mur=
let tableau_voisins=voisins tableau_mur in
let tab_caseadj=num_voisins tableau_voisins in
let chemin=trajet !case_fantome !case_pacman tab_caseadj in
let shortest dst chemin =
let sc=sup chemin in
if sc.(Array.length sc -1)=0 && 0!=dst then
Array.sub sc 0 (Array.length sc -1)
else
sc
in
shortest dst chemin;;

(*-----------------------------Fantome-----------------------------*)

let fromto src dst=
if dst=(src+largeur) then
deplacementEntity (case_fantome,couleur_fantome) largeur
else if dst=(src-largeur) then
deplacementEntity (case_fantome,couleur_fantome) (-largeur)
else if dst=(src-1) then
deplacementEntity (case_fantome,couleur_fantome) (-1)
else
deplacementEntity (case_fantome,couleur_fantome) 1;;

let fantome tableau_mur =
Graphics.set_color (rgb 255 0 0);
afficheEntity (case_fantome,couleur_fantome);
Graphics.set_color (rgb 0 0 0);
while true do begin
Unix.sleep 1;
let chemin= chemin !case_fantome !case_pacman tableau_mur in
fromto !case_fantome chemin.(1);
if !case_pacman= !case_fantome then begin
Printf.printf "%s\n" "PERDU !!!";
exit 0;
end
end;
done;;

(*-----------------------------Fonction Jeu-----------------------------*)
let _=
let tableau_mur=generate_lab largeur hauteur in
initialisation tableau_mur;
let _=Thread.create fantome tableau_mur in
while !case_pacman != (largeur*hauteur -1) do
mouvement tableau_mur;
done;
Printf.printf "%s\n" "GAGNER !!!";
exit 0;