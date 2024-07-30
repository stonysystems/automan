let curry (f: ('a * 'b) -> 'c) (x: 'a) (y: 'b) =
  f (x, y)

module Result : sig
  include module type of Result
  val ( let< ): ('a, 'e) result -> ('a -> ('b, 'e) result) -> ('b, 'e) result
  val map2: ('a -> 'b) -> ('c -> 'd) -> ('a, 'c) t -> ('b, 'd) t
end = struct
  include Result
  let ( let< ) = bind

  let map2 f g =
    fold
      ~ok:(fun x -> Result.Ok (f x))
      ~error:(fun y -> Result.Error (g y))
end

module List : sig
  include module type of List
  val take: int -> 'a list -> 'a list
  val unsnoc: 'a list -> 'a list * 'a

  (* TODO: Find decent OCaml monad library *)
  val mapMResult: ('a -> ('b, 'e) Result.t) -> 'a list -> ('b list, 'e) Result.t
end = struct
  include List

  let take n l =
    let[@tail_mod_cons] rec aux n l =
      match n, l with
      | 0, _ | _, [] -> []
      | n, x::l -> x::aux (n - 1) l
    in
    if n < 0 then invalid_arg "List.take";
    aux n l

  let unsnoc xs =
    match (rev xs) with
    | [] -> invalid_arg "List.unsnoc"
    | (last :: sx) -> (rev sx, last)

  let mapMResult f xs =
    let rec aux (accum: 'b list) (xs: 'a list) =
      match xs with
      | [] -> Result.Ok accum
      | x :: xs' ->
        match f x with
        | Result.Ok y -> aux (y :: accum) xs'
        | Result.Error e -> Result.Error e
    in
    Result.map List.rev (aux [] xs)
end

module NonEmptyList = struct
  type 'a t = ( :: ) of 'a * 'a list
  [@@deriving show, eq]

  let head (xs: 'a t): 'a =
    let ( :: ) (hd, _) = xs in
    hd

  let singleton (x: 'a): 'a t = (::) (x, [])

  let coerce (xs: 'a list): 'a t =
    match xs with
    | [] -> invalid_arg "NonEmptyList.coerce: arg is empty"
    | x :: xs' -> (::) (x, xs')

  let as_list (xs: 'a t): 'a list =
    let ( :: ) (x, xs) = xs in
    x :: xs

  let cons (x: 'a) (xs: 'a t): 'a t =
    let ( :: ) (x', xs') = xs in
    (::) (x, x' :: xs')

  let unsnoc (xs: 'a t): 'a list * 'a =
    List.unsnoc (as_list xs)

  let map (f: 'a -> 'b) (xs: 'a t): 'b t =
    let ( :: ) (hd, tl) = xs in
    f hd :: List.map f tl

  let fold_left_1 (f: 'a -> 'a -> 'a) (xs: 'a t) =
    let ( :: ) (h, t) = xs in
    List.fold_left f h t

  let fold_right_1 (f: 'a -> 'a -> 'a) (xs: 'a t) =
    let rec aux (y: 'a) (ys: 'a list) =
      match ys with
      | [] -> y
      | y1 :: ys -> f y (aux y1 ys)
    in
    let ( :: ) (x, xs) = xs in
    aux x xs
end

module Either : sig
  include module type of Either
  type ('a, 'b) t = ('a, 'b) Either.t
  [@@deriving show, eq]
end = struct
  include Either
  type ('a, 'b) t = ('a, 'b) Either.t =
    | Left  of 'a
    | Right of 'b
  [@@deriving show, eq]
end

module State : sig
  type ('s, 'a) t = 's -> 'a * 's

  val ( let* ) : ('s, 'a) t -> ('a -> ('s, 'b) t) -> ('s, 'b) t
  val return : 'a -> ('s, 'a) t

  val gets : ('s -> 'a) -> ('s, 'a) t
  val get  : ('s, 's) t
  val puts : ('s -> 's) -> ('s, unit) t
  val put  : 's -> ('s, unit) t

  val run  : ('s, 'a) t -> 's -> 'a
end = struct
  type ('s, 'a) t = 's -> 'a * 's

  let ( let* ) f g = fun s ->
    let (x, s') = f s in
    g x s'

  let return x = fun s -> (x, s)

  let gets f = fun s -> (f s, s)
  let get = fun s -> gets (fun x -> x) s
  let puts f = fun s -> ((), f s)
  let put s = puts (fun _ -> s)

  let run prog st =
    let (x, _) = prog st in x
end

module StateError : sig
  type ('s, 'e, 'a) t = ('s, ('a, 'e) Result.t) State.t
  val bind: ('s, 'e, 'a) t -> ('a -> ('s, 'e, 'b) t) -> ('s, 'e, 'b) t
  val return: 'a -> ('s, 'e, 'a) t
  val map: ('a -> 'b) -> ('s, 'e, 'a) t -> ('s, 'e, 'b) t

  val error: 'e -> ('s, 'e, 'a) t
  val map_error: ('e -> 'f) -> ('s, 'e, 'a) t -> ('s, 'f, 'a) t

  val get: ('s, 'e, 's) t
  val put: 's -> ('s, 'e, unit) t
  val puts: ('s -> ('s, 'e) Result.t) -> ('s, 'e, unit) t
end = struct
  type ('s, 'e, 'a) t = ('s, ('a, 'e) Result.t) State.t

  let bind f g = fun s ->
    let (scrut, s') = f s in
    match scrut with
    | Result.Error msg -> (Result.Error msg, s')
    | Result.Ok x -> g x s'

  let return x = fun s -> (Result.Ok x, s)

  let map f x = bind x (fun y -> return (f y))

  let error e = fun s ->
    (Result.Error e, s)

  let map_error err prog = fun s ->
    let (res, s') = prog s in
    (Result.map_error err res, s')

  let get = fun s -> (Result.Ok s, s)
  let put s = fun _ -> (Result.Ok (), s)
  let puts f = fun s ->
    match f s with
    | Result.Ok s' -> (Result.Ok (), s')
    | Result.Error msg -> (Result.Error msg, s)
end

;;
