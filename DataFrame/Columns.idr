module DataFrame.Columns

import public Data.Vect
import Decidable.Equality

import DataFrame.Utils
import DataFrame.Vector
import public DataFrame.Row
import public DataFrame.Signature

public export
data Columns : Nat -> Sig -> Type where
  Nil : Columns n Nil
  (::) : Vect n a -> Columns n sig -> Columns n ((cn :- a) :: sig)

export
(++) : {sig : Sig} -> Columns m sig -> Columns n sig -> Columns (m + n) sig
(++) {sig = []} [] [] = []
(++) {sig = (cn :- a) :: sig} (xs :: cs) (xs' :: cs') = (xs ++ xs') :: cs ++ cs'

export
reverse : {sig : Sig} -> Columns n sig -> Columns n sig
reverse {sig = []} [] = []
reverse {sig = (cn :- a) :: sig} (xs :: cs) = reverse xs :: reverse cs

export
empty : {sig : Sig} -> Columns 0 sig
empty {sig = []} = []
empty {sig = (cn :- a) :: sig} = [] :: empty

export
deepMap : {sig : Sig}
    -> (p : Type -> Type)
    -> (f : {0 a : Type} -> Vect n a -> Vect m (p a))
    -> Columns n sig
    -> Columns m (Map p sig)
deepMap {sig = []} p f [] = []
deepMap {sig = (cn :- a) :: sig} p f (xs :: cols) = f xs :: deepMap p f cols

export
map : {sig : Sig}
    -> (f : {0 a : Type} -> Vect n a -> Vect m a)
    -> Columns n sig -> Columns m sig
map {sig} f cols = rewrite sym (sigMapId sig) in deepMap (\x => x) f cols

export
where_ : {sig : Sig} -> Columns n sig -> (mask : Vect n Bool) -> Columns (trueCount mask) sig
where_ {sig = []} [] mask = []
where_ {sig = (cn :- a) :: sig} (xs :: cols) mask = (xs `where_` mask) :: (cols `where_` mask)

export
uncons : {sig : Sig} -> Columns (S n) sig -> (Row sig, Columns n sig)
uncons {sig = []} [] = ([], [])
uncons {sig = (cn :- a) :: sig} ((x :: xs) :: cols) =
  case uncons cols of
    (firstRow, rest) => (x :: firstRow, xs :: rest)

export
toRows : {n : Nat} -> {sig : Sig} -> Columns n sig -> List (Row sig)
toRows {n = Z  } cols = []
toRows {n = S _} cols = case uncons cols of
  (row, rest) => row :: toRows rest

export
extract :
    Columns rowCount sig
    -> InSig cn a sig
    -> Vect rowCount a
extract (xs :: cols)  Here      = xs
extract (xs :: cols) (There pf) = extract cols pf

namespace StableSort
  export
  sortBy : (cmp : a -> a -> Ordering) -> (xs : List a) -> List a
  sortBy cmp []  = []
  sortBy cmp [x] = [x]
  sortBy cmp xs  = let (x, y) = split xs in
      mergeBy cmp
            (StableSort.sortBy cmp (assert_smaller xs x))
            (StableSort.sortBy cmp (assert_smaller xs y)) -- not structurally smaller, hence assert
    where
      splitRec : List b -> List a -> (List a -> List a) -> (List a, List a)
      splitRec (_::_::xs) (y::ys) zs = splitRec xs ys (zs . ((::) y))
      splitRec  _             ys  zs = (ys, zs [])

      split : List a -> (List a, List a)
      split xs = splitRec xs xs id

-- TODO: do this properly
vecSortBy : (a -> a -> Ordering) -> Vect n a -> Vect n a
vecSortBy p xs = rewrite pf in fromList sorted
where
  pf : n = List.length sorted
  pf = believe_me (Refl {x = n})

  sorted : List a
  sorted = StableSort.sortBy p (toList xs)

permute : Ord a => Vect n a -> Vect n b -> Vect n b
permute perm = map snd . vecSortBy (\x, y => fst x `compare` fst y) . zip perm

export
orderBy : Ord a => ({0 b : Type} -> Vect n b -> Vect n b) -> Vect n a -> Columns n sig -> Columns n sig
orderBy f perm [] = []
orderBy f perm (col :: cols) = f (permute perm col) :: orderBy f perm cols

insert : {sig : Sig} -> (cn : String) -> Vect n a -> Columns n sig -> Columns n (insert cn a sig)
insert cn xs [] = [xs]
insert {sig = (cn' :- a') :: sig'} cn xs (xs' :: xss') with (decEq cn cn')
  insert {sig = (cn  :- a') :: sig'} cn xs (xs' :: xss') | Yes Refl = xs  :: xss'
  insert {sig = (cn' :- a') :: sig'} cn xs (xs' :: xss') | No  _    = xs' :: insert cn xs xss'

export
overrideWith : {sig, sig' : Sig} -> Columns n sig -> Columns n sig' -> Columns n (sig `overrideWith` sig')
overrideWith {sig' = []} xss [] = xss
overrideWith {sig' = (cn' :- a') :: sig'} xss (xs' :: xss') = insert cn' xs' xss `overrideWith` xss'
