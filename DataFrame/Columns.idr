module DataFrame.Columns

import public DataFrame.Core

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
map : {sig : Sig} -> ({a : Type} -> Vect n a -> Vect m a) -> Columns n sig -> Columns m sig
map {sig = []} f [] = []
map {sig = cn :- a :: sig} f (xs :: cols) = f xs :: map f cols

export
where_ : {sig : Sig} -> Columns n sig -> (mask : Vect n Bool) -> Columns (trueCount mask) sig
where_ {sig = []} [] mask = []
where_ {sig = cn :- a :: sig} (xs :: cols) mask = (xs `where_` mask) :: (cols `where_` mask)
