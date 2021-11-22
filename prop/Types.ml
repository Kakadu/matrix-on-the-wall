open OCanren
open Format

module Tuple = struct
  type ground = GT.string OCanren.Std.List.ground
  [@@deriving gt ~options:{ gmap; show; foldl; fmt }]

  type logic = GT.string OCanren.logic OCanren.Std.List.logic
  [@@deriving gt ~options:{ gmap; show; foldl; fmt }]

  type nonrec injected = (ground, logic) OCanren.injected

  let reify eta : injected -> logic = OCanren.Std.List.reify OCanren.reify eta
end

[%%distrib
type nonrec ('self, 'tuple, 'name) t =
  | Mlt of 'self * 'self
  | Proj of 'self * 'tuple
  | Rotate of 'self
  | Expand of 'self * 'name
  | Var of 'tuple
[@@deriving gt ~options:{ gmap; show; foldl; fmt }]

type ground = (ground, Tuple.ground, GT.string) t]

type injected = (ground, logic) OCanren.injected

let make_var xs : injected = var (Std.list ( !! ) xs)

let rec gced_to_vars xs ys =
  let open OCanren.Std in
  conde
    [ xs === Std.nil () &&& (xs === ys)
    ; xs === Std.nil () &&& (ys =/= Std.nil ()) &&& failure
    ; fresh
        (h1 h2 t1 t2)
        (xs === h1 % t1)
        (conde
           [ ys === h2 % t2 &&& (h1 === h2) &&& gced_to_vars t1 t2; gced_to_vars t1 ys ])
    ]
;;

let test_gced_to_vars ?(expectok = true) start fin =
  let xs =
    OCanren.(run q) (fun _ -> gced_to_vars start fin) (fun x -> x#reify reify)
    |> Stream.take
  in
  (* Format.printf "%d\n%!" (List.length xs); *)
  if expectok then [] <> xs else [] = xs
;;

let%test _ = test_gced_to_vars (Std.list ( !! ) []) (Std.list ( !! ) [])
let%test _ = test_gced_to_vars (Std.list ( !! ) [ "a" ]) (Std.list ( !! ) [])
let%test _ = test_gced_to_vars (Std.list ( !! ) [ "a"; "b" ]) (Std.list ( !! ) [])
let%test _ = test_gced_to_vars (Std.list ( !! ) [ "a"; "b" ]) (Std.list ( !! ) [ "b" ])
let%test _ = test_gced_to_vars (Std.list ( !! ) [ "a"; "b" ]) (Std.list ( !! ) [ "a" ])
(* let%test _ = test_gced_to_vars (Std.list ( !! ) [ "a"; "b" ]) (Std.list ( !! ) [ "d" ]) *)

let is_a_var e contents =
  let open OCanren.Std in
  fresh
    (a b c)
    (e === var contents)
    (* (contents =/= Std.nil ()) *)
    (conde
       [ fresh h (contents === !<h)
       ; fresh (h g) (contents === h % !<g)
       ; fresh (h g f) (contents === h % (g % !<f))
       ])
;;

let flip f a b = f b a

let hackf msg var =
  debug_var var (flip reify) (function
      | [ st ] ->
        Format.printf "%s = %a\n%!" msg (GT.fmt logic) st;
        success
      | _ -> failwith "should not happen")
;;

let rec gced_to : injected -> injected -> goal =
 fun start fin ->
  let open OCanren.Std in
  fresh
    ()
    (conde
       [ fresh (v1 v2) (is_a_var start v1) (start === fin)
       ; fresh (e v e2) (start === expand e v) (gced_to e fin)
       ; fresh
           (e1 v2 e3 v4)
           (start === proj e1 v2)
           (conde
              [ gced_to e1 fin; fresh (e3 e4) (fin === proj e3 v4) &&& gced_to e1 e3 ])
       ; fresh e (start === rotate e) (gced_to e fin)
       ; fresh
           (e1 e2 e3 e4)
           (start === mlt e1 e2)
           (fin === mlt e3 e4)
           (gced_to e1 e3)
           (gced_to e2 e4)
         (* ; fresh
           (e1 e2 e3 e4)
           (start === mlt e1 e2)
           (conde [ fin === mlt e3 e4 &&& gced_to e1 e3 &&& gced_to e2 e4 ]) *)
       ])
;;

let test_gced_to ?(expectok = true) start fin =
  let xs =
    OCanren.(run q) (fun _ -> gced_to start fin) (fun x -> x#reify reify) |> Stream.take
  in
  Format.printf "%d\n%!" (List.length xs);
  if expectok then [] <> xs else [] = xs
;;

(*
include (
  struct
    let x = var (Std.list ( !! ) [ "x" ])
    let y = var (Std.list ( !! ) [ "y" ])
    let (_ : injected) = expand x !!"z"

    let%test _ = test_gced_to (mlt (expand x !!"z") (expand y !!"z")) (mlt x y)
  end :
    sig end) *)

let rotate_incr xs ys =
  let open Std in
  conde
    [ xs === Std.nil () &&& (ys === xs)
    ; fresh (h tl) (xs === h % tl) (List.appendo tl !<h ys)
    ]
;;

let rotate_decr xs ys = rotate_incr ys xs

let rec evalo (start : injected) (rez : Tuple.injected) =
  let open OCanren.Std in
  conde
    [ fresh
        (e1 e2 r1 r2 x y z tl)
        (start === mlt e1 e2)
        (evalo e1 r1)
        (evalo e2 r2)
        (r1 === x % (y % tl))
        (r2 === y % (z % tl))
        (rez === x % (z % tl))
    ; fresh (e n r) (start === expand e n) (evalo e r) (Std.List.appendo r !<n rez)
    ; fresh (e2 xs) (start === rotate e2) (evalo e2 xs) (rotate_decr xs rez)
    ; fresh () (is_a_var start rez)
    ]
;;

let evalo_no_proj = evalo

let evalo_proj start fin =
  let open OCanren.Std in
  let rec mymembero xs v rez =
    conde
      [ xs === Std.nil () &&& (rez === !!false)
      ; fresh
          (h tl)
          (xs === h % tl)
          (conde [ h === v &&& (rez === !!true); h =/= v &&& mymembero tl v rez ])
      ]
  in
  let rec is_subset big small rez =
    conde
      [ small === nil () &&& (rez === !!true)
      ; big === nil () &&& (small =/= nil ()) &&& (rez === !!false)
      ; fresh
          (sh stl rez0)
          (small === sh % stl)
          (mymembero big sh rez0)
          (conde
             [ rez0 === !!false &&& (rez === !!false)
             ; rez0 === !!true &&& is_subset big stl rez
             ])
      ]
  in
  fresh
    (e1 e2 v1 v2 rez0)
    (start === proj e1 v2)
    (evalo_no_proj e1 v1)
    (is_subset v1 v2 rez0)
    (conde [ rez0 === !!true &&& (fin === v2); rez0 === !!false &&& (fin === nil ()) ])
;;

let synth : Tuple.injected -> injected -> injected -> goal =
 fun v emult ans ->
  fresh
    ()
    (* (evalo_proj ans v)
    (hackf " candidate evaluates right " ans)
    (gced_to ans emult) *)
    (gced_to ans emult)
    (* (hackf " simplifies right " ans) *)
    (evalo_proj ans v)
;;
