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

  -- summarisation
  Summarise : (List a -> b) -> Expr Many sig a -> Expr One sig b

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
summarise : (List a -> b) -> Expr Many sig a -> Expr One sig b
summarise = Summarise

export
maximum : Ord a => a -> Expr Many sig a -> Expr One sig a
maximum e = summarise $ foldr max e

export
minimum : Ord a => a -> Expr Many sig a -> Expr One sig a
minimum e = summarise $ foldr min e

export
sum : Num a => Expr Many sig a -> Expr One sig a
sum = summarise sum

export
product : Num a => Expr Many sig a -> Expr One sig a
product = summarise product

export
count : Expr Many sig a -> Expr One sig Int
count = summarise $ cast . length

public export
EvalTy : Quantity -> Nat -> Type -> Type
EvalTy Many n a = Vect n a
EvalTy One  n a = a

export
eval : {q : Quantity} -> (df : DF sig) -> Expr q sig a -> EvalTy q (rowCount df) a
eval {q = Many} df (L x) = replicate (rowCount df) x
eval {q = One}  df (L x) = x
eval {q = Many} df (V cn) = df ^. cn
eval {q = Many} df (Map f xs) = map f (eval df xs)
eval {q = One}  df (Map f xs) = f (eval df xs)
eval {q = Many} df (Ap fs xs) = zipWith id (eval df fs) (eval df xs)
eval {q = One}  df (Ap fs xs) = (eval df fs) (eval df xs)
eval {q = Many} df (BinOp f xs ys) = zipWith f (eval df xs) (eval df ys)
eval {q = One}  df (BinOp f xs ys) = f (eval df xs) (eval df ys)
