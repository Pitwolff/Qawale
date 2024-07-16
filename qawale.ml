type position = {plateau : int list array array; mutable coups : ((int * int) * int list * position) list; tour : int; galets_restants : int}

let copy plateau = 
  Array.init (Array.length plateau) (fun i -> Array.init (Array.length plateau.(i)) (fun j -> plateau.(i).(j)))

let calculer_coups p = 
  let res = ref [] in
  let rec aux plat i j pile chemin i1 j1 = match pile with
    | a::q -> if i <> 0 && (chemin = [] || List.hd chemin <> 3) then begin
                let plat2 = copy plat in
                plat2.(i - 1).(j) <- a::plat2.(i - 1).(j);
                if q = [] then 
                  res := ((i1, j1), 0::chemin, {plateau = plat2; coups = []; tour = -p.tour; galets_restants = p.galets_restants - 1})::!res
                else 
                  aux plat2 (i - 1) j q (0::chemin) i1 j1
              end;
              if i <> Array.length plat - 1 && (chemin = [] || List.hd chemin <> 0) then begin
                let plat2 = copy plat in
                plat2.(i + 1).(j) <- a::plat2.(i + 1).(j);
                if q = [] then 
                  res := ((i1, j1), 3::chemin, {plateau = plat2; coups = []; tour = -p.tour; galets_restants = p.galets_restants - 1})::!res
                else 
                  aux plat2 (i + 1) j q (3::chemin) i1 j1
              end;
              if j <> 0 && (chemin = [] || List.hd chemin <> 2) then begin
                let plat2 = copy plat in
                plat2.(i).(j - 1) <- a::plat2.(i).(j - 1);
                if q = [] then 
                  res := ((i1, j1), 1::chemin, {plateau = plat2; coups = []; tour = -p.tour; galets_restants = p.galets_restants - 1})::!res
                else 
                  aux plat2 i (j - 1) q (1::chemin) i1 j1
              end;
              if j <> Array.length plat.(i) - 1 && (chemin = [] || List.hd chemin <> 1) then begin
                let plat2 = copy plat in
                plat2.(i).(j + 1) <- a::plat2.(i).(j + 1);
                if q = [] then 
                  res := ((i1, j1), 2::chemin, {plateau = plat2; coups = []; tour = -p.tour; galets_restants = p.galets_restants - 1})::!res
                else 
                  aux plat2 i (j + 1) q (2::chemin) i1 j1
              end
    | _ -> failwith "pile vide"
  in
  for i = 0 to Array.length p.plateau - 1 do
    for j = 0 to Array.length p.plateau.(i) - 1 do
      if p.plateau.(i).(j) <> [] then 
        let plat = copy p.plateau in
        plat.(i).(j) <- [];
        aux plat i j (List.rev (p.tour::p.plateau.(i).(j))) [] i j
    done
  done;
  !res

let heuristique p = 
  let res = ref 0 in
  let n = Array.length p.plateau in
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      if p.plateau.(i).(j) <> [] then
        res := !res + List.hd p.plateau.(i).(j)
    done
  done;
  for i = 0 to n - 1 do
    if p.plateau.(i).(0) <> [] then begin
      let j = ref 1 in
      let c = List.hd p.plateau.(i).(0) in
      while !j <> n && p.plateau.(i).(!j) <> [] && List.hd p.plateau.(i).(!j) = c do
        incr j
      done;
      res := !res + c * !j;
      if !j = n then res := !res + n * n * c end
  done;
  for i = 0 to n - 1 do
    if p.plateau.(i).(n - 1) <> [] then begin
      let j = ref 1 in
      let c = List.hd p.plateau.(i).(n - 1) in
      while !j <> n && p.plateau.(i).(n - 1 - !j) <> [] && List.hd p.plateau.(i).(n - 1 - !j) = c do
        incr j
      done;
      res := !res + c * !j;
      if !j = n then res := !res + n * n * c end
  done;
  for j = 0 to n - 1 do
    if p.plateau.(0).(j) <> [] then begin
      let i = ref 1 in
      let c = List.hd p.plateau.(0).(j) in
      while !i <> n && p.plateau.(!i).(j) <> [] && List.hd p.plateau.(!i).(j) = c do
        incr i
      done;
      res := !res + c * !i;
      if !i = n then res := !res + n * n * c end
  done;
  for j = 0 to n - 1 do
    if p.plateau.(n - 1).(j) <> [] then begin
      let i = ref 1 in
      let c = List.hd p.plateau.(n - 1).(j) in
      while !i <> n && p.plateau.(n - 1 - !i).(j) <> [] && List.hd p.plateau.(n - 1 - !i).(j) = c do
        incr i
      done;
      res := !res + c * !i;
      if !i = n then res := !res + n * n * c end
  done;
  if p.plateau.(0).(0) <> [] then begin
    let i = ref 1 in
    let c = List.hd p.plateau.(0).(0) in
    while !i <> n && p.plateau.(!i).(!i) <> [] && List.hd p.plateau.(!i).(!i) = c do
      incr i
    done;
    res := !res + c * !i;
    if !i = n then res := !res + n * n * c end;
  if p.plateau.(n - 1).(n - 1) <> [] then begin
    let i = ref 1 in
    let c = List.hd p.plateau.(n - 1).(n - 1) in
    while !i <> n && p.plateau.(n - 1 - !i).(n - 1 - !i) <> [] && List.hd p.plateau.(n - 1 - !i).(n - 1 - !i) = c do
      incr i
    done;
    res := !res + c * !i;
    if !i = n then res := !res + n * n * c end;
  if p.plateau.(n - 1).(0) <> [] then begin
    let i = ref 1 in
    let c = List.hd p.plateau.(n - 1).(0) in
    while !i <> n && p.plateau.(n - 1 - !i).(!i) <> [] && List.hd p.plateau.(n - 1 - !i).(!i) = c do
      incr i
    done;
    res := !res + c * !i;
    if !i = n then res := !res + n * n * c end;
  if p.plateau.(0).(n - 1) <> [] then begin
    let i = ref 1 in
    let c = List.hd p.plateau.(0).(n - 1) in
    while !i <> n && p.plateau.(!i).(n - 1 - !i) <> [] && List.hd p.plateau.(!i).(n - 1 - !i) = c do
      incr i
    done;
    res := !res + c * !i;
    if !i = n then res := !res + n * n * c end;
  !res

let est_final p = 
  let vic = Array.make 2 false in
  let n = Array.length p.plateau in
  for i = 0 to n - 1 do
    if p.plateau.(i).(0) <> [] then begin
      let j = ref 1 in
      let c = List.hd p.plateau.(i).(0) in
      if c <> 0 then begin
        while !j <> n && p.plateau.(i).(!j) <> [] && List.hd p.plateau.(i).(!j) = c do
          incr j
        done;
        if !j = n then 
          vic.((-c + 1) / 2) <- true
      end
    end
  done;
  for j = 0 to n - 1 do
    if p.plateau.(0).(j) <> [] then begin
      let i = ref 1 in
      let c = List.hd p.plateau.(0).(j) in
      if c <> 0 then begin
        while !i <> n && p.plateau.(!i).(j) <> [] && List.hd p.plateau.(!i).(j) = c do
          incr i
        done;
        if !i = n then 
          vic.((-c + 1) / 2) <- true
      end
    end
  done;
  if p.plateau.(0).(0) <> [] then begin
    let i = ref 1 in
    let c = List.hd p.plateau.(0).(0) in
    if c <> 0 then begin
      while !i <> n && p.plateau.(!i).(!i) <> [] && List.hd p.plateau.(!i).(!i) = c do
        incr i
      done;
      if !i = n then vic.((-c + 1) / 2) <- true 
    end
  end;
  if p.plateau.(n - 1).(0) <> [] then begin
    let i = ref 1 in
    let c = List.hd p.plateau.(n - 1).(0) in
    if c <> 0 then begin
    while !i <> n && p.plateau.(n - 1 - !i).(!i) <> [] && List.hd p.plateau.(n - 1 - !i).(!i) = c do
      incr i
    done;
    if !i = n then vic.((-c + 1) / 2) <- true
    end
  end;
  if vic.(0) && vic.(1) then (true, 0)
  else if vic.(0) then (true, max_int)
  else if vic.(1) then (true, min_int)
  else (false, 0)

let rec evaluation dic p profondeur a b = 
  if Hashtbl.mem dic p then Hashtbl.find dic p else begin
  let (final, eval) = est_final p in
  if final then begin 
    Hashtbl.add dic p (p.tour * (eval / (p.galets_restants + 1)));
    p.tour * (eval / (p.galets_restants + 1))
  end
  else if profondeur = 0 || p.galets_restants = 0 then begin
    let v = p.tour * heuristique p in
    Hashtbl.add dic p v;
    v
  end
  else begin 
    let v = fst (strategie dic p profondeur a b) in
    Hashtbl.add dic p v;
    v
  end end

and strategie dic p profondeur a b = 
  p.coups <- calculer_coups p;
  List.fold_left (fun (eval, coup) (depart, chemin, pos_suiv) -> 
    if eval >= b then (eval, coup)
    else begin let eval2 = -evaluation dic pos_suiv (profondeur - 1) (-b) (-eval) in
    if eval2 > eval then (eval2, (depart, chemin, pos_suiv)) else (eval, coup) end)
    (-evaluation dic (let (_, _, pos) = List.hd p.coups in pos) (profondeur - 1) (-b) (-a), List.hd p.coups) (List.tl p.coups)

let afficher plateau = 
  print_newline ();
  Array.iter (fun t -> Array.iter 
  (fun l -> if l = [] then print_string "X " 
            else begin 
              let x = List.hd l in 
              if x = 0 then print_string "J " 
              else if x = 1 then print_string "R " 
              else print_string "B " 
            end) t; print_newline ()) plateau;
  print_newline ()

let partie profondeur = 
  let plat = Array.make_matrix 4 4 [] in
  plat.(0).(0) <- 0::0::[];
  plat.(3).(0) <- 0::0::[];
  plat.(0).(3) <- 0::0::[];
  plat.(3).(3) <- 0::0::[];
  let p = ref {plateau = plat; coups = []; tour = 1; galets_restants = 16} in
  afficher !p.plateau;
  while !p.galets_restants <> 0 && not (fst (est_final !p)) do
    let (eval, ((i, j), chemin, pos_suiv)) = strategie (Hashtbl.create 1) !p profondeur (min_int + 1) max_int in
    print_int i; print_int j; print_char ' ';
    List.iter print_int (List.rev chemin);
    print_newline ();
    p := pos_suiv;
    afficher !p.plateau;
    Printf.printf "score : %d\n\n" (-eval * !p.tour);
  done;
  let score = snd (est_final !p) in
  if score = 0 then print_string "égalité\n"
  else if score = max_int then print_string "victoire rouge\n"
  else print_string "victoire blanc\n"

let () = partie 3
