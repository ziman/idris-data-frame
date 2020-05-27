module DataFrame.Ops

import Data.Vect

import DataFrame.Columns
import DataFrame.Vector

import public DataFrame.DataFrame
import public DataFrame.Utils
import public DataFrame.Expr

%default total

infixl 3 ~>
public export
(~>) : a -> (a -> b) -> b
(~>) x f = f x

export
where_ : {sig : Sig} -> (Expr Many sig Bool) -> (df : DF sig) -> DF sig
where_ p df = MkDF (columns df `where_` (df ^- p))

export
head : {sig : Sig} -> Nat -> DF sig -> DF sig
head n (MkDF cols) = MkDF (map (take n) cols)

export
uncons : {sig : Sig} -> (df : DF sig) -> Maybe (Row sig, DF sig)
uncons (MkDF {rowCount = Z} cols) = Nothing
uncons (MkDF {rowCount = S n} cols) =
  case uncons cols of
     (row, rest) => Just (row, MkDF rest)

selectCols : {sig : Sig} -> SigF (Expr Many sig) newSig -> (df : DF sig) -> Columns (rowCount df) newSig
selectCols [] df = []
selectCols ((cn :- e) :: es) df = (df ^- e) :: selectCols es df

export
select : {sig : Sig} -> SigF (Expr Many sig) newSig -> DF sig -> DF newSig
select es df = MkDF (selectCols es df)

export
modify : {sig, addSig : Sig} -> SigF (Expr Many sig) addSig -> DF sig -> DF (sig `overrideWith` addSig)
modify es df = MkDF $ columns df `overrideWith` selectCols es df

public export
data OrderBy : Sig -> Type where
  Asc : Ord a => Expr Many sig a -> OrderBy sig
  Desc : Ord a => Expr Many sig a -> OrderBy sig

orderStep : OrderBy sig -> DF sig -> DF sig
orderStep (Asc  e) df = MkDF $ orderBy id      (df ^- e) (columns df)
orderStep (Desc e) df = MkDF $ orderBy reverse (df ^- e) (columns df)

export
orderBy : {sig : Sig} -> List (OrderBy sig) -> DF sig -> DF sig
orderBy xs df = foldr orderStep df xs
