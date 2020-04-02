module DataFrame.Summarise

import DataFrame.Vector
import DataFrame.Ops
import public DataFrame.Expr

%default total

namespace Ords
  public export
  data Ords : (Type -> Type) -> Type where
    Nil : Ords f
    (::) : Ord a => f a -> Ords f -> Ords f

public export
GroupBy : Sig -> Type
GroupBy sig = Ords (Expr Many sig)

namespace Breaks
  public export
  data Breaks : Nat -> Type where
    One : (n : Nat) -> Breaks n
    (::) : (n : Nat) -> Breaks r -> Breaks (n + r)

namespace Groups
  public export
  data Groups : Sig -> (n : Nat) -> Breaks n -> Type where
    One : {b : Nat} -> Columns b sig -> Groups sig b (One b)
    (::) : {b : Nat} -> Columns b sig -> Groups sig n bs -> Groups sig (b + n) (b :: bs)

export
record GroupedDF (sig : Sig) where
  constructor GDF
  {rowCount : Nat}
  {breaks : Breaks rowCount}
  groups : Groups sig rowCount breaks

breaksCol : Ord a => Vect n a -> Vect n Bool
breaksCol (x :: y :: xs) = (x /= y) :: breaksCol (y :: xs)
breaksCol [x] = [False]
breaksCol [] = []

breaksCols : {n : Nat} -> Ords (Vect n) -> Vect n Bool
breaksCols [] = replicate n False
breaksCols [col] = breaksCol col -- saves one zipWith
breaksCols (col :: cols) = breaksCol col || breaksCols cols

breaks : (bs : Vect n Bool) -> Breaks n
breaks [] = One Z
breaks (True  :: bs) = 1 :: breaks bs
breaks (False :: bs) =
  case breaks bs of
    One n => One (S n)
    n :: ns => S n :: ns

groupCount : Breaks n -> Nat
groupCount (One _) = 1
groupCount (_ :: bs) = S (groupCount bs)

infix 3 ^=
(^=) : (df : DF sig) -> Ords (Expr Many sig) -> Ords (Vect (rowCount df))
(^=) df [] = []
(^=) df (e :: es) = (df ^- e) :: (df ^= es)

break : {sig : Sig} -> (bs : Breaks n) -> Columns n sig -> Groups sig n bs
break (One n) cols = One cols
break (b :: bs) cols =
  case takeRows b cols of
    (grp, rest) => grp :: break bs rest

toOrder : GroupBy sig -> List (OrderBy sig)
toOrder [] = []
toOrder (e :: es) = Asc e :: toOrder es

export
groupBy : {sig : Sig} -> GroupBy sig -> DF sig -> GroupedDF sig
groupBy gbs df =
  let df' = orderBy (toOrder gbs) df
    in GDF $ break (breaks (breaksCols (df' ^= gbs))) (columns df')

summariseCol : Expr One sig a -> Groups sig n bs -> Vect (groupCount bs) a
summariseCol e (One grp) = [MkDF grp ^- e]
summariseCol e (grp :: grps) = (MkDF grp ^- e) :: summariseCol e grps

summariseCols : SigF (Expr One sig) sig' -> Groups sig n bs -> Columns (groupCount bs) sig'
summariseCols [] gs = []
summariseCols ((cn :- e) :: es) gs = summariseCol e gs :: summariseCols es gs

export
summarise : {sig, sig' : Sig} -> SigF (Expr One sig) sig' -> GroupedDF sig -> DF sig'
summarise es (GDF gs) = MkDF (summariseCols es gs)
