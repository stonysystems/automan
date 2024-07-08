let curry (f: ('a * 'b) -> 'c) (x: 'a) (y: 'b) =
  f (x, y)

module List : sig
  include module type of List
  val take: int -> 'a list -> 'a list
  val unsnoc: 'a list -> 'a list * 'a

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
end

module NonEmptyList = struct
  type 'a t = ( :: ) of 'a * 'a list
  [@@deriving show, eq]

  let singleton (x: 'a): 'a t = (::) (x, [])

  let coerce (xs: 'a list): 'a t =
    match xs with
    | [] -> invalid_arg "NonEmptyList.coerce: arg is empty"
    | x :: xs' -> (::) (x, xs')

  let as_list (xs: 'a t): 'a list =
    let ( :: ) (x, xs) = xs in
    x :: xs

  let unsnoc (xs: 'a t): 'a list * 'a =
    List.unsnoc (as_list xs)

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

;;
