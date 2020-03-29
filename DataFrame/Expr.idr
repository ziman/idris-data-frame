module DataFrame.Expr

import public Data.Vect

import public DataFrame.DataFrame
import public DataFrame.Signature

%default total

export
data Expr : Nat -> Sig -> Type -> Type where
  L : a -> Expr n sig a
  Ls : Vect n a -> Expr n sig a
  V : (cn : String) -> InSig cn a sig => Expr n sig a
  Map : (a -> b) -> Expr n sig a -> Expr n sig b
  Ap : Expr n sig (a -> b) -> Expr n sig a -> Expr n sig b

  -- special common case for efficiency
  BinOp : (a -> b -> c) -> Expr n sig a -> Expr n sig b -> Expr n sig c

export
Functor (Expr n sig) where
  map = Map

export
Applicative (Expr n sig) where
  pure = L
  (<*>) = Ap

export
Num a => Num (Expr n sig a) where
  (+) = BinOp (+)
  (*) = BinOp (*)
  fromInteger = pure . fromInteger

export
Neg a => Neg (Expr n sig a) where
  negate = map negate
  (-) = BinOp (-)

export
Fractional a => Fractional (Expr n sig a) where
  (/) = BinOp (/)
  recip = map recip

(==) : Eq a => Expr n sig a -> Expr n sig a -> Expr n sig Bool
(==) = BinOp (==)

(/=) : Eq a => Expr n sig a -> Expr n sig a -> Expr n sig Bool
(/=) = BinOp (/=)

(>) : Ord a => Expr n sig a -> Expr n sig a -> Expr n sig Bool
(>) = BinOp (>)

(>=) : Ord a => Expr n sig a -> Expr n sig a -> Expr n sig Bool
(>=) = BinOp (>=)

(<) : Ord a => Expr n sig a -> Expr n sig a -> Expr n sig Bool
(<) = BinOp (<)

(<=) : Ord a => Expr n sig a -> Expr n sig a -> Expr n sig Bool
(<=) = BinOp (<=)

(&&) : Expr n sig Bool -> Expr n sig Bool -> Expr n sig Bool
(&&) = BinOp (\x, y => x && Delay y)

(||) : Expr n sig Bool -> Expr n sig Bool -> Expr n sig Bool
(||) = BinOp (\x, y => x || Delay y)

export
eval : (df : DF sig) -> Expr (rowCount df) sig a -> Vect (rowCount df) a
eval df (L x) = replicate (rowCount df) x
eval df (Ls xs) = xs
eval df (V cn) = df ^. cn
eval df (Map f xs) = map f (eval df xs)
eval df (Ap fs xs) = zipWith id (eval df fs) (eval df xs)
eval df (BinOp f xs ys) = zipWith f (eval df xs) (eval df ys)
