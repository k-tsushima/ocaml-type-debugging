type expr = Int of int
          | Float of float
          | App of expr * expr
          | Lambda of string * expr

type t = TInt
       | TFloat
       | TFun of t * t
       | TVar of t option ref

exception UnifyError of t * t
               
let new_t () = TVar(ref None)

let rec unify t1 t2 = match (t1, t2) with
  | (TInt, TInt) -> ()
  | (TFloat, TFloat) -> ()
  | (TFun(t1, t2), TFun(t3, t4)) -> unify t1 t3; unify t2 t4
  | (TVar(r), t) | (t, TVar(r))-> (match !r with
                     | None -> r := Some(t) 
                     | Some(t2) -> unify t2 t)
  | _ -> raise (UnifyError(t1, t2))

let test_unify1 = try (unify TInt (TFun(TInt, TInt)); false) with (UnifyError(_)) -> true
let test_unify2 = (unify TInt (new_t ())) = ()
let test_unify3 = (unify (TFun(TInt, TInt)) (new_t ())) = ()

let rec env_get env st = match env with
  | [] -> raise Not_found
  | (a, b) :: rest -> if a = st then b else (env_get rest st)

let test_env1 = try(ignore(env_get [] "st"); false) with Not_found -> true
let test_env2 = env_get [("st", 3)] "st" = 3
let test_env2 = try(ignore(env_get [("k", 3); ("m", 4)] "st"); false)
                with Not_found -> true

let rec remove_env env st = match env with
  | [] -> []
  | (a, b) :: rest -> if a = st then rest else (a, b) :: (remove_env rest st)

let test_remove_env1 = remove_env [(1,2);(2,3)] 2 = [(1,2)]
let test_remove_env2 = remove_env [(1,2);(2,3)] 3 = [(1,2);(2,3)]
let test_remove_env3 = remove_env [(1,2);(2,3)] 1 = [(2,3)]
               
(* normal type inference *)
(* infer: (string * t) list * expr -> env * t *)
let rec infer env expr = match expr with
  | Int(i) -> (env, TInt)
  | Float(f) -> (env, TFloat)
  | App(e1, e2) -> let (env, t1) = infer env e1 in
                   let (env, t2) = infer env e2 in
                   let a = new_t () in
                   unify (TFun(t2, a)) t1;
                   (env, a)
  | Lambda(st, e) ->
     let a = new_t () in
     let (env, t1) = infer ((st, a)::env) e in
     let t2 = env_get env st in
     (remove_env env st, TFun(t2, t1))

let test_infer1 = (infer [] (Int(3))) = ([], TInt)
let test_infer2 = (match (infer [("x", TInt)] (Lambda ("x", Int(5)))) with
                   | ([("x", TInt)], TFun(TVar(_), TInt)) -> true
                   | _ -> false)
let test_infer3 = (match (infer [] (App((Lambda ("x", Int(5))), Int(6)))) with
                   | ([], TInt) -> true
                   | _ -> false)
let test_infer4 = try(ignore(infer [] (App(Int(3), Int(4)))); false) with UnifyError(TFun(_), TInt) -> true | _ -> false
let test_infer5 = try(ignore(infer [] (App(Int(3), App(Float(2.0), Float(3.0))))); false) with UnifyError(TFun(_), TFloat) -> true | _ -> false


let store = ref []

(* If (continuation expr) causes a type error, 
   apply_k throws the continuation away
   & stores type conflict information in "store"
   & returns the new generated type *)
let apply_k k expr v =
  try (k v) with
    UnifyError(t1, t2) ->
     store := (expr, t1, t2) :: !store;
     let (env, _) = v in (env, new_t ())  
     
(* CPS inference *)
let rec infer_cps env expr k = match expr with
  | Int(i) -> apply_k k expr (env, TInt)
  | Float(i) -> apply_k k expr (env, TFloat)
  | App(e1, e2) -> apply_k k expr (infer_cps env e1
                     (fun k1 ->
                       let (env, t1) = k1 in
                       infer_cps env e2
                         (fun k2 ->
                           let (env, t2) = k2 in
                           let a = new_t () in
                           unify (TFun(t2, a)) t1;
                           (env, a))))
  | Lambda(st, e) ->
     apply_k k expr (let a = new_t () in
     infer_cps ((st, a)::env) e (fun k1 -> let (env, t1) = k1 in
                                       let t2 = env_get env st in
                                       (remove_env env st, TFun(t2, t1))))

let init () = store := []

let test_infer_cps1 = infer_cps [] (Int(3)) (fun k -> k)
let test_infer_cps2 = infer_cps [("x", TInt)] (Lambda ("x", Int(5))) (fun k -> k)
let test_infer_cps3 = infer_cps [] (App((Lambda ("x", Int(5))), Int(6))) (fun k -> k)
let test_infer_cps4 = infer_cps [] (App(Int(3), Int(4))) (fun k -> k)
let test_infer_cps5 = infer_cps [] (App(App(Int(3), Int(5)), App(Float(2.0), Float(3.0)))) (fun k -> k)                       

