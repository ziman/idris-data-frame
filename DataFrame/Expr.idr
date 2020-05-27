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
  Count : Num a => Expr q sig a

  Map : (a -> b) -> Expr q sig a -> Expr q sig b
  BinOp : (a -> b -> c) -> Expr q sig a -> Expr q sig b -> Expr q sig c

  Aggregate : (List a -> b) -> Expr Many sig a -> Expr One sig b

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
  (<*>) = BinOp id

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
aggregate : (List a -> b) -> Expr Many sig a -> Expr One sig b
aggregate = Aggregate

export
maximum : Ord a => a -> Expr Many sig a -> Expr One sig a
maximum e = aggregate $ foldr max e

export
minimum : Ord a => a -> Expr Many sig a -> Expr One sig a
minimum e = aggregate $ foldr min e

export
sum : Num a => Expr Many sig a -> Expr One sig a
sum = aggregate sum

export
product : Num a => Expr Many sig a -> Expr One sig a
product = aggregate product

export
length : Expr Many sig a -> Expr One sig Int
length = aggregate $ cast . length

export
count : Num a => Expr q sig a
count = Count

public export
EvalTy : Quantity -> Nat -> Type -> Type
EvalTy Many n a = Vect n a
EvalTy One  n a = a

infix 3 ^-
export
(^-) : {q : Quantity} -> (df : DF sig) -> Expr q sig a -> EvalTy q (rowCount df) a
(^-) {q = Many} df (L x) = replicate (rowCount df) x
(^-) {q = One}  df (L x) = x
(^-) {q = Many} df (V cn) = df ^. cn
(^-) {q = Many} df (Map f xs) = map f (df ^- xs)
(^-) {q = One}  df (Map f xs) = f (df ^- xs)
(^-) {q = Many} df (BinOp f xs ys) = zipWith f (df ^- xs) (df ^- ys)
(^-) {q = One}  df (BinOp f xs ys) = f (df ^- xs) (df ^- ys)
(^-) {q = One}  df Count = fromInteger . cast $ rowCount df
(^-) {q = Many} df Count = replicate (rowCount df) (fromInteger . cast $ rowCount df)
(^-) {q = One} df (Aggregate f e) = f $ toList (df ^- e)
