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

namespace GroupBy
  public export
  data GroupBy : Sig -> Type where
    Nil : GroupBy sig
    (::) : (o : Ord a) => (cn : String) -> (is : InSig cn a sig) => GroupBy sig -> GroupBy sig

namespace Values
  public export
  data Values : GroupBy sig -> Type where
    Nil : Values []
    (::) : (o : Ord a) => (is : InSig cn a sig) => a -> Values ks -> Values ((::) {o} cn {is} ks)

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
  keys : GroupBy sig
  groups : Groups sig rowCount breaks

namespace Diff
  public export
  data Diff : Nat -> Type -> Type where
    None : Diff Z a
    One : a -> Diff (S Z) a
    New : a -> Diff (S n) a -> Diff (S (S n)) a
    Old :      Diff (S n) a -> Diff (S (S n)) a

breaksCol : Ord a => Vect n a -> Diff n a
breaksCol [] = None
breaksCol [x] = One x
breaksCol (x :: y :: xs) =
  if x == y
     then Old   $ breaksCol (y :: xs)
     else New x $ breaksCol (y :: xs)

PrevTy : Nat -> Type -> Type -> Type
PrevTy    Z  a b = ()
PrevTy (S n) a b = (a, b)

mergeBreaks : (o : Ord a) => (is : InSig cn a sig) => {gs : GroupBy sig}
  -> Diff n a -> Diff n (Values gs) -> (PrevTy n a (Values gs), Diff n (Values ((::) {o} cn {is} gs)))
mergeBreaks None None = ((), None)
mergeBreaks (One x) (One ys) = ((x,ys), One (x :: ys))
mergeBreaks (New x xd) (New ys ysd) =
  let ((_,_),pd) = mergeBreaks xd ysd
    in ((x,ys), New (x :: ys) pd)
mergeBreaks (Old xd) (New ys ysd) =
  let ((px,_),pd) = mergeBreaks xd ysd
    in ((px,ys), New (px :: ys) pd)
mergeBreaks (New x xd) (Old ysd) =
  let ((_,pys),pd) = mergeBreaks xd ysd
    in ((x,pys), New (x :: pys) pd)
mergeBreaks (Old xd) (Old ysd) =
  let ((px,pys),pd) = mergeBreaks xd ysd
    in ((px,pys), Old pd)

emptyDiff : (n : Nat) -> Diff n (Values [])
emptyDiff Z = None
emptyDiff (S Z) = One []
emptyDiff (S (S n)) = Old $ emptyDiff (S n)

diff : (gb : GroupBy sig) -> (df : DF sig) -> Diff (rowCount df) (Values gb)
diff [] df = emptyDiff _
diff ((::) {is} cn cns) df = snd $
  mergeBreaks {is} (breaksCol (df ^. cn)) (diff cns df)

{-
breaksCols : {n : Nat} -> Ords (Named . Vect (S n)) -> Vect n (Ords Maybe)
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

infix 3 ^:
(^:) : (df : DF sig) -> (gb : GroupBy sig) -> Values (Named . Vect (rowCount df)) gb
(^:) df [] = []
(^:) df (cn :: cns) = (cn :- (df ^. cn)) :: (df ^: cns)
-}

{-
break : {sig : Sig} -> (bs : Breaks n) -> Columns n sig -> Groups sig n bs
break (One n) cols = One cols
break (b :: bs) cols =
  case takeRows b cols of
    (grp, rest) => grp :: break bs rest

toOrder : GroupBy sig -> List (OrderBy sig)
toOrder [] = []
toOrder (cn :: cns) = Asc (col cn) :: toOrder cns

export
groupBy : {sig : Sig} -> GroupBy sig -> DF sig -> GroupedDF sig
groupBy gbs df =
  let df' = orderBy (toOrder gbs) df
      bs  = df' ^: gbs
    in GDF gbs (break (breaks (breaksCols bs)) (columns df'))

summariseCol : Expr One sig a -> Groups sig n bs -> Vect (groupCount bs) a
summariseCol e (One grp) = [MkDF grp ^- e]
summariseCol e (grp :: grps) = (MkDF grp ^- e) :: summariseCol e grps

summariseCols : SigF (Expr One sig) sig' -> Groups sig n bs -> Columns (groupCount bs) sig'
summariseCols [] gs = []
summariseCols ((cn :- e) :: es) gs = summariseCol e gs :: summariseCols es gs

export
summarise : {sig, sig' : Sig} -> SigF (Expr One sig) sig' -> GroupedDF sig -> DF sig'
summarise es (GDF ks gs) = MkDF (summariseCols es gs)
-}
