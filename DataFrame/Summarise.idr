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
    (::) : {a : Type} -> (o : Ord a) => (cn : String) -> (is : InSig cn a sig) => GroupBy sig -> GroupBy sig

namespace Values
  public export
  data Values : GroupBy sig -> Type where
    Nil : Values []
    (::) : (o : Ord a) => (is : InSig cn a sig) => a -> Values ks -> Values ((::) {o} cn {is} ks)

namespace Breaks
  public export
  data Breaks : GroupBy sig -> Nat -> Type where
    None : Breaks gb Z
    One : (nMinus1 : Nat) -> Values gb -> Breaks gb (S nMinus1)
    More : (nMinus1 : Nat) -> Values gb -> Breaks gb r -> Breaks gb (S nMinus1 + r)

namespace Groups
  public export
  data Groups : (n : Nat) -> Breaks gb n -> Type where
    None : Groups Z None
    One :
        {sig : Sig}
        -> {gb : GroupBy sig}
        -> {bs : Breaks gb (S bMinus1)}
        -> (keys : Values gb)
        -> Columns (S bMinus1) sig
        -> Groups (S bMinus1) (One bMinus1 keys)
    More : 
        {sig : Sig}
        -> {gb : GroupBy sig}
        -> {bs : Breaks gb n}
        -> (keys : Values gb)
        -> Columns (S bMinus1) sig
        -> Groups n bs
        -> Groups (S bMinus1 + n) (More bMinus1 keys bs)

export
record GroupedDF (sig : Sig) (gb : GroupBy sig) where
  constructor GDF
  {rowCount : Nat}
  breaks : Breaks gb rowCount
  groups : Groups rowCount breaks

namespace Diff
  public export
  data Diff : Nat -> Type -> Type where
    None : Diff Z a
    One : a -> Diff (S Z) a
    New : a -> Diff (S n) a -> Diff (S (S n)) a
    Old :      Diff (S n) a -> Diff (S (S n)) a

diffCol : Ord a => Vect n a -> Diff n a
diffCol [] = None
diffCol [x] = One x
diffCol (x :: y :: xs) =
  if x == y
     then Old   $ diffCol (y :: xs)
     else New x $ diffCol (y :: xs)

PrevTy : Nat -> Type -> Type -> Type
PrevTy    Z  a b = ()
PrevTy (S n) a b = (a, b)

mergeDiffs : (o : Ord a) => (is : InSig cn a sig) => {gs : GroupBy sig}
  -> Diff n a -> Diff n (Values gs) -> (PrevTy n a (Values gs), Diff n (Values ((::) {o} cn {is} gs)))
mergeDiffs None None = ((), None)
mergeDiffs (One x) (One ys) = ((x,ys), One (x :: ys))
mergeDiffs (New x xd) (New ys ysd) =
  let ((_,_),pd) = mergeDiffs xd ysd
    in ((x,ys), New (x :: ys) pd)
mergeDiffs (Old xd) (New ys ysd) =
  let ((px,_),pd) = mergeDiffs xd ysd
    in ((px,ys), New (px :: ys) pd)
mergeDiffs (New x xd) (Old ysd) =
  let ((_,pys),pd) = mergeDiffs xd ysd
    in ((x,pys), New (x :: pys) pd)
mergeDiffs (Old xd) (Old ysd) =
  let ((px,pys),pd) = mergeDiffs xd ysd
    in ((px,pys), Old pd)

emptyDiff : (n : Nat) -> Diff n (Values [])
emptyDiff Z = None
emptyDiff (S Z) = One []
emptyDiff (S (S n)) = Old $ emptyDiff (S n)

diff : (gb : GroupBy sig) -> (df : DF sig) -> Diff (rowCount df) (Values gb)
diff [] df = emptyDiff _
diff ((::) {is} cn cns) df = snd $
  mergeDiffs {is} (diffCol (df ^. cn)) (diff cns df)

breaks : Diff n (Values gb) -> Breaks gb n
breaks None = None
breaks (One row) = One Z row
breaks (New row d) = More Z row $ breaks d
breaks (Old d) = case breaks d of
  One nMinus1 row => One (S nMinus1) row
  More nMinus1 row bs => More (S nMinus1) row bs

groupCount : Breaks gb n -> Nat
groupCount None = Z
groupCount (One nMinus1 row) = 1
groupCount (More nMinus1 row bs) = S (groupCount bs)

break : {sig : Sig} -> {gb : GroupBy sig} -> (bs : Breaks gb n) -> Columns n sig -> Groups n bs
break None cols = None
break (One nMinus1 keys) cols = One {bs = One nMinus1 keys} keys cols
break (More nMinus1 keys bs) cols =
  case takeRows (S nMinus1) cols of
    (grp, rest) => More keys grp $ break bs rest

toOrder : GroupBy sig -> List (OrderBy sig)
toOrder [] = []
toOrder (cn :: cns) = Asc (col cn) :: toOrder cns

export
groupBy : {sig : Sig} -> (gb : GroupBy sig) -> DF sig -> GroupedDF sig gb
groupBy gb df = 
  let df' = orderBy (toOrder gb) df
      d   = diff gb df'
      bs  = breaks d
      gs  = break bs (columns df')
    in GDF {sig} bs gs

summariseCol : {gb : GroupBy sig} -> {bs : Breaks gb n}
    -> Expr One sig a -> Groups n bs -> Vect (groupCount bs) a
summariseCol e None = []
summariseCol e (One keys grp) = [MkDF grp ^- e]
summariseCol e (More keys grp grps) = (MkDF grp ^- e) :: summariseCol e grps

summariseCols : {gb : GroupBy sig} -> SigF (Expr One sig) sig' -> (bs : Breaks gb n) -> Groups n bs
    -> Columns (groupCount bs) sig'
summariseCols [] bs gs = []
summariseCols ((cn :- e) :: es) bs gs = summariseCol e gs :: summariseCols es bs gs

public export
keySig : GroupBy sig -> Sig
keySig [] = []
keySig ((::) {a} cn cns) = (cn :- a) :: keySig cns

fromValues : Values gb -> Row (keySig gb)
fromValues [] = []
fromValues (x :: xs) = x :: fromValues xs

keyColumns : {sig : Sig} -> {gb : GroupBy sig} -> {bs : Breaks gb n}
    -> (gs : Groups n bs)
    -> Columns (groupCount bs) (keySig gb)
keyColumns None = empty
keyColumns (One keys _) = singleton $ fromValues keys
keyColumns (More keys _ gs) = cons (fromValues keys) (keyColumns gs)

summarise' :
    {sig, sig' : Sig}
    -> SigF (Expr One sig) sig'
    -> {gb : GroupBy sig}
    -> (bs : Breaks gb n)
    -> (gs : Groups n bs)
    -> Columns (groupCount bs) (keySig gb `overrideWith` sig')
summarise' es bs gs = keyColumns gs `overrideWith` summariseCols es bs gs

export
summarise : {sig, sig' : Sig}
    -> SigF (Expr One sig) sig'
    -> {gb : GroupBy sig}
    -> (gdf : GroupedDF sig gb)
    -> DF (keySig gb `overrideWith` sig')
summarise es (GDF bs gs) = MkDF (summarise' es bs gs)
