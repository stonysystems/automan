let curry (f: ('a * 'b) -> 'c) (x: 'a) (y: 'b) =
  f (x, y)

module List : sig
  include module type of List
  val take: int -> 'a list -> 'a list
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
end

module NonEmptyList = struct
  type 'a t = ( :: ) of 'a * 'a list
  [@@deriving show, eq]

  let singleton (x: 'a): 'a t = (::) (x, [])

  let coerce (xs: 'a list): 'a t =
    match xs with
    | [] -> assert false
    | x :: xs' -> (::) (x, xs')
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
