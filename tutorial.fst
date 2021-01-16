module Welcome

open FStar.All
open FStar.ST

type filename = string

let canWrite (f : filename) : bool =
    match f with
    | "demo/tempfile" -> true
    | _               -> false

let canRead (f : filename) : bool =
    canWrite f ||
    f = "demo/README"
    
//val read : f : filename{canRead f} -> ML string
//let read f = FStar.IO.print_string ("Dummy read of file " ^ f ^ "\n"); f

let read (f : filename{canRead f}) : ML string =
    FStar.IO.print_string ("Wut da " ^ f ^ "\n"); f
    
let write (f : filename{canWrite f}) (s : string) : ML unit =
    FStar.IO.print_string
        ("Dummy write of string " ^ s ^ " to file " ^ f ^ "\n")

let passwd : filename = "demo/password"
let readme : filename = "demo/README"
let tmp    : filename = "demo/tempfile"

let staticChecking (_ : unit) : ML unit =
    let v1 = read tmp    in
    let v2 = read readme in
    //let v3 = read passwd in
    write tmp "GENERAL KENOBI! HELLO THERE"
    //;write passwd "lol junk"

exception InvalidRead

let checkedRead (f : filename) : ML string =
    if canRead f
    then read f
    else raise InvalidRead
    
exception InvalidWrite

let checkedWrite (f : filename) (s : string) : ML unit =
    if canWrite f
    then write f s
    else raise InvalidWrite

let dynamicChecking (_ : unit) : ML unit =
    
    let v1 = checkedRead tmp    in
    let v2 = checkedRead readme in
    let v3 = checkedRead passwd in
    
    checkedWrite tmp    "GENERAL KENOBI! HELLO THERE";
    checkedWrite passwd "lol junk"

(*let new_counter (i : int) : St (unit -> St int) =
    let c = ST.alloc i in
    fun _ -> (c := !c + 1); !c
*)

let isPositive (i : int) : bool = i > 0
let max (i j : int) : int =
    if i > j then i else j
    
let _ = assert (max 0 1 = 1)

let _ = assert (forall x y.
                    max x y >= x &&
                    max x y >= y &&
                    (max x y = x || max x y = y))

open FStar.Mul

let rec fact (n : nat) : nat =
    if n = 0
    then 1
    else n * fact (n - 1)
    
let rec factorial_is_positive
    (n : nat) : GTot (u : unit{fact n > 0}) =
        match n with
        | 0 -> ()
        | _ -> factorial_is_positive (n - 1)

(*
val factorial_gt_arg_ugliest :
    n : (n : nat{n > 2}) -> GTot (u : unit{fact n > n})

val factorial_gt_arg_still_ugly :
    n : nat{n > 2} -> GTot (u : unit{fact n > n})
*)

val factorial_gt_arg_nice :
    n : nat{n > 2} -> Lemma (fact n > n)
let rec factorial_gt_arg_nice n =
    match n with
        | 3 -> ()
        | _ -> factorial_gt_arg_nice (n - 1)

(*
val factorial_gt_arg_nice_v2 :
    n : nat -> Lemma (requires (n > 2))
                     (ensures (fact n > n))
*)

(* Exercise 3c *)
let rec fib (n : nat) : nat =
    if n <= 1
    then 1
    else fib (n - 2) + fib (n - 1)

let rec fib_gt_arg (n : nat{n >= 2}) : Lemma (fib n >= n) =
    if n = 2
    then ()
    else fib_gt_arg (n - 1)

let fib_gt_arg' (n : nat{n >= 2}) : Lemma (fib n >= n) =
    if n = 2
    then ()
    else admit ()

(*
type mylist 'a =
    | Nil : mylist 'a
    | Cons : hd : 'a -> tl : mylist 'a -> mylist 'a
*)

let rec len (l : list 'a) : nat =
    match l with
    | []     -> 0
    | _ :: t -> 1 + len t

val app : #a : Type -> list a -> list a -> list a
let rec app (l1 l2 : list 'a) : list 'a =
//    : (r : list 'a{len r = len l1 + len l2}) =
    match l1 with
    | []     -> l2
    | h :: t -> h :: (app t l2)

let rec app_assoc
    (l1 l2 l3 : list 'a)
    : Lemma (app (app l1 l2) l3 == app l1 (app l2 l3)) =
    match l1 with
    | []     -> ()
    | _ :: t -> app_assoc t l2 l3

let rec len_app (l1 l2 : list 'a) :
    Lemma (len (app l1 l2) = len l1 + len l2) =
    match l1 with
    | [] -> ()
    | _ :: t -> len_app t l2

let rec mem
    (#a : eqtype) (x : a) (l : list a) : bool =
    match l with
    | []     -> false
    | h :: t -> x = h || mem x t

let rec mem_app
    (#a : eqtype) (x : a) (l1 l2 : list a)
    : Lemma (mem x (app l1 l2) = mem x l1 || mem x l2) =
    match l1 with
    | []     -> ()
    | _ :: t -> mem_app x t l2

let rec mem_app2
    (#a : eqtype) (x : a) (l1 l2 : list a)
    : Lemma (mem x (app l1 l2) <==> mem x l1 || mem x l2) =
    match l1 with
    | []     -> ()
    | _ :: t -> mem_app2 x t l2

let rec rev (#a : Type) (l : list a) : list a =
    match l with
    | []     -> []
    | h :: t -> app (rev t) [h]

let snoc l h = app l [h]

let rec rev_snoc
    (l : list 'a) (x : 'a)
    : Lemma (rev (snoc l x) == x :: rev l) =
    match l with
    | []     -> ()
    | h :: t -> rev_snoc t x

(*
let rec rev_app
    (#a : Type) (l1 l2 : list a) :
    
    Lemma (rev (app l1 l2) == app (rev l2) (rev l1))
    
    =
    match l1 with
    | []     -> ()
    | h :: t ->
        rev_app t l2;
        app_assoc (rev l2) (rev t) [h];
        rev_snoc t h
*)

let rec rev_rev
    (#a : Type) (l : list a)
    : Lemma (rev (rev l) == l) =
    match l with
    | []     -> ()
    | h :: t -> rev_snoc (rev t) h; rev_rev t

let rec snoc_inj
    (x y : 'a) (l : list 'a)
    : Lemma (requires (snoc l x == snoc l y))
            (ensures  (x == y))
    =
    match l with
    | []     -> ()
    | _ :: t -> snoc_inj x y t

let rec snoc_inj'
    (x y : 'a) (l1 l2 : list 'a) :
        
    Lemma (requires (snoc l1 x == snoc l2 y))
          (ensures  (l1 == l2 /\ x == y))
    =
    match l1, l2 with
    | []      , []       -> ()
    | _ :: _  , []       -> ()
    | []      , _ :: _   -> ()
    | h1 :: t1, h2 :: t2 -> snoc_inj' x y t1 t2

let rec rev_inj
    (l1 l2 : list 'a) :
    
    Lemma (requires (rev l1 == rev l2))
          (ensures  (l1 == l2))
    =
    match l1, l2 with
    | []      , []       -> ()
    | []      , _ :: _   -> ()
    | _ :: _  , []       -> ()
    | h1 :: t1, h2 :: t2 ->
        snoc_inj' h1 h2 (rev t1) (rev t2);
        rev_inj t1 t2

let rev_inj'
    (l1 l2 : list 'a) :

    Lemma (requires (rev l1 == rev l2))
          (ensures  (l1 == l2))
    =
    rev_rev l1; rev_rev l2

let rec map (f : 'a -> 'b) (l : list 'a) : list 'b =
    match l with
    | []     -> []
    | h :: t -> f h :: map f t

let rec find (f : 'a -> bool) (l : list 'a) : option 'a =
    match l with
    | []     -> None
    | h :: t -> if f h then Some h else find f t

let sSome_inj (x y : 'a) :
    Lemma (requires (Some x == Some y))
          (ensures  (x == y))
    =
    ()
    
let rec find_Some
    (f : 'a -> bool) (l : list 'a) :
    
    Lemma (match find f l with
           | None   -> true
           | Some x -> f x)
    =
    match l with
    | []     -> ()
    | h :: t -> find_Some f t
    
let rec find_Some_v2
    (f : 'a -> bool) (l : list 'a) :
    
    Lemma (None? (find f l) || f (Some?.v (find f l)))
    =
    match l with
    | []     -> ()
    | h :: t -> find_Some_v2 f t

let rec find' (f : 'a -> bool) (l : list 'a)
    : option (x : 'a{f x}) =
    match l with
    | []     -> None
    | h :: t -> if f h then Some h else find' f t

let rec foldl
    (f : 'b -> 'a -> 'a) (l : list 'b) (a : 'a) : 'a =
    match l with
    | []     -> a
    | h :: t -> foldl f t (f h a)

let rec app_nil_r (l : list 'a) : Lemma (app l [] == l) =
    match l with
    | []     -> ()
    | _ :: t -> app_nil_r t

let rec app_cons_r
    (l1 l2 : list 'a) (x : 'a) :

    Lemma (app l1 (x :: l2) == app (snoc l1 x) l2)
    =
    match l1 with
    | []     -> ()
    | h :: t -> app_cons_r t l2 x
    
let rec foldl_cons
    (l1 l2 : list 'a) :
    
    Lemma (foldl Cons l1 l2 == app (rev l1) l2)
    =
    match l1 with
    | []     -> ()
    | h :: t ->
        foldl_cons t (h :: l2);
        app_cons_r (rev t) l2 h

(*
let foldl_nil_cons_rev (l : list 'a) :
    Lemma (foldl Cons l [] == rev l) =
        foldl_cons l []; app_nil_r l
*)

let hd (l : list 'a{Cons? l}) : 'a =
    match l with
    | h :: _ -> h

let tl (l : list 'a{Cons? l}) : list 'a =
    match l with
    | _ :: t -> t

let rec nth (n : nat) (l : list 'a) : option 'a =
    match l with
    | []     -> None
    | h :: t -> if n = 0 then Some h else nth (n - 1) t

let rec nth' (n : nat) (l : list 'a{n < len l}) : 'a =
    match l with
    | h :: t -> if n = 0 then h else nth' (n - 1) t

(* 5: Proving Termination *)

let rec ack (m n : nat) : nat =
    if m = 0
    then n + 1
    else
        if n = 0
        then ack (m - 1) 1
        else ack (m - 1) (ack m (n - 1))
        
val ack' : n : nat -> m : nat -> Tot nat (decreases %[m; n])
let rec ack' (n m : nat) : nat =
    if m = 0
    then n + 1
    else
        if n = 0
        then ack' 1 (m - 1)
        else ack' (ack' (n - 1) m) (m - 1)

(* Exercise 5a: *)
let rec rev' (l1 l2 : list 'a) : list 'a =
    match l1 with
    | []     -> l2
    | h :: t -> rev' t (h :: l2)

let rec rev'_spec
    (l1 l2 : list 'a) :
    
    Lemma (rev' l1 l2 == app (rev l1) l2)
    =
    match l1 with
    | []     -> ()
    | h :: t -> rev'_spec t (h :: l2); app_assoc (rev t) [h] l2

let rec fib' (a b n : nat) : Tot nat (decreases n) =
    match n with
    | 0 -> a
    | 1 -> b
    | _ -> fib' b (a + b) (n - 1)


// fib' (fib k)       (fib (k + 1)) n       == (def)
// fib' (fib (k + 1)) (fib (k + 2)) (n - 1) == (IH)
// fib  ((k + 1) + (n - 1))                 == (properties of +)
// fib  (k + n)
let rec fib'_is_fib
    (n k : nat) :
        
    Lemma (fib' (fib k) (fib (k + 1)) n == fib (k + n))
    =
    match n with
    | 0 -> ()
    | 1 -> ()
    | _ -> fib'_is_fib (n - 1) (k + 1)
