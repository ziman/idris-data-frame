module DataFrame.Ops

import Data.Vect

import DataFrame.Columns

import public DataFrame.DataFrame
import public DataFrame.Utils
import public DataFrame.Vector

%default total

export
where_ : {sig : Sig} -> ((df : DF sig) -> Vect (rowCount df) Bool) -> DF sig -> DF sig
where_ p df = MkDF (columns df `where_` p df)

export
head : {sig : Sig} -> Nat -> DF sig -> DF sig
head n (MkDF columns) = MkDF (map (take n) columns)
