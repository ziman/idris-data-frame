module DataFrame.Expr

import public Data.Vect

import public DataFrame.DataFrame
import public DataFrame.Signature

%default total

public export
data Quantity = One | Many

export
data Expr : Quantity -> Sig -> Type -> Type where
  L : a -> Expr q sig a
  V : (cn : String) -> InSig cn a sig => Expr Many sig a

  -- free applicative functor
  Map : (a -> b) -> Expr q sig a -> Expr q sig b
  Ap : Expr q sig (a -> b) -> Expr q sig a -> Expr q sig b

  -- special common case for efficiency
  BinOp : (a -> b -> c) -> Expr q sig a -> Expr q sig b -> Expr q sig c

export
val : a -> Expr q sig a
val = L

export
col : (cn : String) -> InSig cn a sig => Expr Many sig a
col = V

export
Functor (Expr q sig) where
  map = Map

export
Applicative (Expr q sig) where
  pure = L
  (<*>) = Ap

export
Num a => Num (Expr q sig a) where
  (+) = BinOp (+)
  (*) = BinOp (*)
  fromInteger = pure . fromInteger

export
Neg a => Neg (Expr q sig a) where
  negate = map negate
  (-) = BinOp (-)

export
Fractional a => Fractional (Expr q sig a) where
  (/) = BinOp (/)
  recip = map recip

export
Integral a => Integral (Expr q sig a) where
  div = BinOp div
  mod = BinOp mod

export
(==) : Eq a => Expr q sig a -> Expr q sig a -> Expr q sig Bool
(==) = BinOp (==)

export
(/=) : Eq a => Expr q sig a -> Expr q sig a -> Expr q sig Bool
(/=) = BinOp (/=)

export
(>) : Ord a => Expr q sig a -> Expr q sig a -> Expr q sig Bool
(>) = BinOp (>)

export
(>=) : Ord a => Expr q sig a -> Expr q sig a -> Expr q sig Bool
(>=) = BinOp (>=)

export
(<) : Ord a => Expr q sig a -> Expr q sig a -> Expr q sig Bool
(<) = BinOp (<)

export
(<=) : Ord a => Expr q sig a -> Expr q sig a -> Expr q sig Bool
(<=) = BinOp (<=)

export
(&&) : Expr q sig Bool -> Expr q sig Bool -> Expr q sig Bool
(&&) = BinOp (\x, y => x && Delay y)

export
(||) : Expr q sig Bool -> Expr q sig Bool -> Expr q sig Bool
(||) = BinOp (\x, y => x || Delay y)

export
eval : (df : DF sig) -> Expr Many sig a -> Vect (rowCount df) a
eval df (L x) = replicate (rowCount df) x
eval df (V cn) = df ^. cn
eval df (Map f xs) = map f (eval df xs)
eval df (Ap fs xs) = zipWith id (eval df fs) (eval df xs)
eval df (BinOp f xs ys) = zipWith f (eval df xs) (eval df ys)
