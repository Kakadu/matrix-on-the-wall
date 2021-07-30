open OCanren
open Tester
open Types

(* let () =
  run_exn (GT.show GT.int) (-1) q qh (REPR (fun q -> q === !!5));
  run_exn (GT.show ground) (-1) q qh (REPR (fun q -> q === trueo))
;; *)

let run_e ?(n = -1) ph =
  let open Types in
  runR Types.reify (GT.show ground) (GT.show logic) n q qh (REPR (fun q -> gced_to ph q))
;;

let reduces_to ?(n = -1) ph =
  let open Types in
  runR Types.reify (GT.show ground) (GT.show logic) n q qh (REPR (fun q -> gced_to ph q))
;;

let reduces_to_check ?(n = -1) ph ph2 =
  let open Types in
  runR
    Types.reify
    (GT.show ground)
    (GT.show logic)
    n
    q
    qh
    (REPR (fun q -> q === ph2 &&& gced_to ph ph2))
;;

let x = var (Std.list ( !! ) [ "x" ])
let y = var (Std.list ( !! ) [ "y" ])

(* let () = run_e (mlt (expand x !!"z") (expand y !!"z")) *)
(* let () = run_e (expand x !!"z") *)

(* Why two answers ?  *)
let () =
  let open Types in
  runR
    Types.reify
    (GT.show ground)
    (GT.show logic)
    10
    q
    qh
    (REPR
       (fun q ->
         (* fresh tmp (q === mlt x tmp)  *)
         gced_to (mlt x y) q
         (* gced_to y q *)))
;;

let () =
  let open Types in
  runR
    Types.reify
    (GT.show ground)
    (GT.show logic)
    10
    q
    qh
    (REPR (fun q -> gced_to (expand x !!"z") q))
;;

let () =
  let open Types in
  runR Types.reify (GT.show ground) (GT.show logic) 10 q qh (REPR (fun q -> gced_to y q))
;;

let synthesize_run ?(n = -1) ph mult =
  let open Types in
  runR
    Types.reify
    (GT.show ground)
    (GT.show logic)
    n
    q
    qh
    (REPR (fun q -> synth ph mult q))
;;

let __ () =
  synthesize_run
    (Std.list ( !! ) [ "x"; "z" ])
    (mlt (make_var [ "x"; "y" ]) (make_var [ "y"; "z" ]))
;;

let __ () =
  let open Types in
  let moo = mlt (make_var [ "x"; "y" ]) (make_var [ "y"; "z" ]) in
  runR
    Types.reify
    (GT.show ground)
    (GT.show logic)
    1
    q
    qh
    (REPR
       (fun q ->
         synth
           (Std.list ( !! ) [ "x"; "z" ])
           moo
           (proj moo (Std.list ( !! ) [ "x"; "z" ]))))
;;

let __ () =
  synthesize_run
    (Std.list ( !! ) [ "x"; "y" ])
    (mlt (make_var [ "x"; "y" ]) (make_var [ "y"; "z" ]))
;;

let () =
  let open Types in
  let open OCanren.Std in
  let xy = make_var [ "x"; "y" ] in
  let yz = make_var [ "y"; "z" ] in
  let rez = Std.list ( !! ) [ "x"; "y" ] in
  let query = mlt xy yz in
  let corr_ans =
    proj (mlt (expand xy !!"z") (rotate (expand yz !!"y"))) (Std.list ( !! ) [ "x"; "y" ])
  in
  runR
    Types.reify
    (GT.show ground)
    (GT.show logic)
    10
    q
    qh
    (REPR (fun q -> gced_to corr_ans query));
  runR
    Tuple.reify
    (GT.show Tuple.ground)
    (GT.show Tuple.logic)
    10
    q
    qh
    (REPR (fun q -> evalo_proj corr_ans q));
  runR
    Tuple.reify
    (GT.show Tuple.ground)
    (GT.show Tuple.logic)
    10
    q
    qh
    (REPR (fun q -> evalo (rotate (expand yz !!"y")) q));
  (* (REPR (fun q -> Std.List.appendo rez !<(!!"z") q)); *)
  runR
    Types.reify
    (GT.show ground)
    (GT.show logic)
    3
    q
    qh
    (REPR (fun q -> synth rez query q))
;;

(* let __ () =
  let open Types in
  runR
    Types.reify
    (GT.show ground)
    (GT.show logic)
    (-1)
    q
    qh
    (REPR (fun q -> gced_to (mlt (make_var [ "x"; "y" ]) (make_var [ "y"; "z" ])) q))
;;

let __ () =
  let open Types in
  runR
    Types.reify
    (GT.show ground)
    (GT.show logic)
    10
    q
    qh
    (REPR (fun q -> gced_to q (mlt (make_var [ "x" ]) (make_var [ "y" ]))))
;;

let __ () =
  let open Types in
  runR
    Types.reify
    (GT.show ground)
    (GT.show logic)
    10
    q
    qh
    (REPR (fun q -> gced_to q (make_var [ "x"; "y" ])))
;;

let __ () =
  let open Types in
  runR
    Tuple.reify
    (GT.show Tuple.ground)
    (GT.show Tuple.logic)
    20
    q
    qh
    (REPR (fun q -> gced_to_vars q (Std.list ( !! ) [ "x"; "y" ])))
;; *)
