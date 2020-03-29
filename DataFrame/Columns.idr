module DataFrame.Columns

import public Data.Vect

import DataFrame.Utils
import DataFrame.Vector
import public DataFrame.Row
import public DataFrame.Signature

public export
data Columns : Nat -> Sig -> Type where
  Nil : Columns n Nil
  (::) : Vect n a -> Columns n sig -> Columns n (cn :- a :: sig)

export
(++) : {sig : Sig} -> Columns m sig -> Columns n sig -> Columns (m + n) sig
(++) {sig = []} [] [] = []
(++) {sig = cn :- a :: sig} (xs :: cs) (xs' :: cs') = (xs ++ xs') :: cs ++ cs'

export
reverse : {sig : Sig} -> Columns n sig -> Columns n sig
reverse {sig = []} [] = []
reverse {sig = cn :- a :: sig} (xs :: cs) = reverse xs :: reverse cs

export
empty : {sig : Sig} -> Columns 0 sig
empty {sig = []} = []
empty {sig = cn :- a :: sig} = [] :: empty

export
deepMap : {sig : Sig}
    -> (p : Type -> Type)
    -> (f : {0 a : Type} -> Vect n a -> Vect m (p a))
    -> Columns n sig
    -> Columns m (Map p sig)
deepMap {sig = []} p f [] = []
deepMap {sig = cn :- a :: sig} p f (xs :: cols) = f xs :: deepMap p f cols

export
map : {sig : Sig}
    -> (f : {0 a : Type} -> Vect n a -> Vect m a)
    -> Columns n sig -> Columns m sig
map {sig} f cols = rewrite sym (sigMapId sig) in deepMap (\x => x) f cols

export
where_ : {sig : Sig} -> Columns n sig -> (mask : Vect n Bool) -> Columns (trueCount mask) sig
where_ {sig = []} [] mask = []
where_ {sig = cn :- a :: sig} (xs :: cols) mask = (xs `where_` mask) :: (cols `where_` mask)

export
uncons : {sig : Sig} -> Columns (S n) sig -> (Row sig, Columns n sig)
uncons {sig = []} [] = ([], [])
uncons {sig = cn :- a :: sig} ((x :: xs) :: cols) =
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
