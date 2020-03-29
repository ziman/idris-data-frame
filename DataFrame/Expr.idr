module DataFrame.Expr

import public Data.Vect

import public DataFrame.DataFrame
import public DataFrame.Signature

%default total

export
data Expr : Sig -> Type -> Type where
  L : a -> Expr sig a
  V : (cn : String) -> InSig cn a sig => Expr sig a

  -- free applicative functor
  Map : (a -> b) -> Expr sig a -> Expr sig b
  Ap : Expr sig (a -> b) -> Expr sig a -> Expr sig b

  -- special common case for efficiency
  BinOp : (a -> b -> c) -> Expr sig a -> Expr sig b -> Expr sig c

export
val : a -> Expr sig a
val = L

export
col : (cn : String) -> InSig cn a sig => Expr sig a
col = V

export
Functor (Expr sig) where
  map = Map

export
Applicative (Expr sig) where
  pure = L
  (<*>) = Ap

export
Num a => Num (Expr sig a) where
  (+) = BinOp (+)
  (*) = BinOp (*)
  fromInteger = pure . fromInteger

export
Neg a => Neg (Expr sig a) where
  negate = map negate
  (-) = BinOp (-)

export
Fractional a => Fractional (Expr sig a) where
  (/) = BinOp (/)
  recip = map recip

export
Integral a => Integral (Expr sig a) where
  div = BinOp div
  mod = BinOp mod

export
(==) : Eq a => Expr sig a -> Expr sig a -> Expr sig Bool
(==) = BinOp (==)

export
(/=) : Eq a => Expr sig a -> Expr sig a -> Expr sig Bool
(/=) = BinOp (/=)

export
(>) : Ord a => Expr sig a -> Expr sig a -> Expr sig Bool
(>) = BinOp (>)

export
(>=) : Ord a => Expr sig a -> Expr sig a -> Expr sig Bool
(>=) = BinOp (>=)

export
(<) : Ord a => Expr sig a -> Expr sig a -> Expr sig Bool
(<) = BinOp (<)

export
(<=) : Ord a => Expr sig a -> Expr sig a -> Expr sig Bool
(<=) = BinOp (<=)

export
(&&) : Expr sig Bool -> Expr sig Bool -> Expr sig Bool
(&&) = BinOp (\x, y => x && Delay y)

export
(||) : Expr sig Bool -> Expr sig Bool -> Expr sig Bool
(||) = BinOp (\x, y => x || Delay y)

export
eval : (df : DF sig) -> Expr sig a -> Vect (rowCount df) a
eval df (L x) = replicate (rowCount df) x
eval df (V cn) = df ^. cn
eval df (Map f xs) = map f (eval df xs)
eval df (Ap fs xs) = zipWith id (eval df fs) (eval df xs)
eval df (BinOp f xs ys) = zipWith f (eval df xs) (eval df ys)
