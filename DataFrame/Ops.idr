module DataFrame.Ops

import Data.Vect

import DataFrame.Columns

import public DataFrame.DataFrame
import public DataFrame.Utils
import public DataFrame.Expr

%default total

infixl 3 ~>
public export
(~>) : a -> (a -> b) -> b
(~>) x f = f x

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

selectCols : {sig : Sig} -> SigF (Expr sig) newSig -> (df : DF sig) -> Columns (rowCount df) newSig
selectCols [] df = []
selectCols ((cn :- e) :: es) df = eval df e :: selectCols es df

export
select : {sig : Sig} -> SigF (Expr sig) newSig -> DF sig -> DF newSig
select es df = MkDF (selectCols es df)

export
modify : {sig, addSig : Sig} -> SigF (Expr sig) addSig -> DF sig -> DF (sig `overrideWith` addSig)
modify es df = MkDF $ columns df `overrideWith` selectCols es df

public export
data OrderBy : Sig -> Type where
  Asc : (cn : String) -> Ord a => InSig cn a sig => OrderBy sig
  Desc : (cn : String) -> Ord a => InSig cn a sig => OrderBy sig

orderStep : OrderBy sig -> DF sig -> DF sig
orderStep (Asc  x) df = MkDF $ orderBy id      (df ^. x) (columns df)
orderStep (Desc x) df = MkDF $ orderBy reverse (df ^. x) (columns df)

export
orderBy : {sig : Sig} -> List (OrderBy sig) -> DF sig -> DF sig
orderBy xs df = foldr orderStep df xs
