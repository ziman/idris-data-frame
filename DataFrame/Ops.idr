module DataFrame.Ops

import Data.Vect

import DataFrame.Columns

import public DataFrame.DataFrame
import public DataFrame.Utils
import public DataFrame.Expr

%default total

export
where_ : {sig : Sig} -> (Expr sig Bool) -> (df : DF sig) -> DF sig
where_ p df = MkDF (columns df `where_` eval df p)

export
head : {sig : Sig} -> Nat -> DF sig -> DF sig
head n (MkDF cols) = MkDF (map (take n) cols)

export
uncons : {sig : Sig} -> (df : DF sig) -> Maybe (Row sig, DF sig)
uncons (MkDF {rowCount = Z} cols) = Nothing
uncons (MkDF {rowCount = S n} cols) =
  case uncons cols of
     (row, rest) => Just (row, MkDF rest)
