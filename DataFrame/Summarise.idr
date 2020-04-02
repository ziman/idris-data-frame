module DataFrame.Summarise

import DataFrame.Vector
import public DataFrame.Expr

%default total

public export
data Ords : (Type -> Type) -> Type where
  Nil : Ords f
  (::) : Ord a => f a -> Ords f -> Ords f

public export
GroupBy : Sig -> Type
GroupBy sig = Ords (Expr Many sig)

data Groups : Nat -> Nat -> Type where
  Stop : Groups Z 1
  Keep : Groups r g -> Groups (S r) g       -- keep adding to the previous group
  Break : Groups r g -> Groups (S r) (S g)  -- start a new group

export
record GroupedDF (sig : Sig) where
  constructor GDF
  {rowCount : Nat}
  breaks : Vect rowCount Bool
  columns : Columns rowCount sig

breaksCol : Ord a => Vect n a -> Vect n Bool
breaksCol (x :: y :: xs) = (x /= y) :: breaksCol (y :: xs)
breaksCol [x] = [False]
breaksCol [] = []

breaks : {n : Nat} -> Ords (Vect n) -> Vect n Bool
breaks [] = replicate n False
breaks [col] = breaksCol col  -- saves one zipWith (||) with False
breaks (col :: cols) = breaksCol col || breaks cols

groupCount : Vect n Bool -> Nat
groupCount [] = 1
groupCount (False :: bs) = groupCount bs
groupCount (True  :: bs) = 1 + groupCount bs

infix 3 ^=
(^=) : (df : DF sig) -> Ords (Expr Many sig) -> Ords (Vect (rowCount df))
(^=) df [] = []
(^=) df (e :: es) = (df ^- e) :: (df ^= es)

export
groupBy : GroupBy sig -> DF sig -> GroupedDF sig
groupBy gbs df = GDF (breaks (df ^= gbs)) (columns df)

{-
-> take exprs to group by
-> generate N columns
-> map each column (S n) to bool (n)
-> or the bools
-> split the columns
-> or maybe do that during summarisation
-}

{-
export
summariseCols : {sig, sig' : Sig} -> SigF (Expr One sig) sig' -> (gs : List (DF sig)) -> Columns (length gs) sig'
summariseCols [] gs = []
summariseCols ((cn :- e) :: es) gs
  = map (^- e) (fromList gs) :: summarise es gs

export
summarise : {sig, sig' : Sig} -> SigF (Expr One sig) sig' -> GroupedDF sig -> DF sig'
summarise es (GDF gs) = MkDF (summarise es gs)
-}
