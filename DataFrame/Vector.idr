module DataFrame.Vector

import public Data.Vect

-- Vectorisable
public export
data VEable : Nat -> Type -> Type -> Type where
  Vector : VEable n a (Vect n a)
  Single : VEable n a a

-- Vectorised expression
export
data VE : Nat -> Type -> Type where
  Lit : Vect n a -> VE n a
  Repeat : (n : Nat) -> a -> VE n a
  ZipWith : (a -> b -> c) -> VE n a -> VE n b -> VE n c

export
eval : VE n a -> Vect n a
eval (Lit xs) = xs
eval (Repeat n x) = replicate n x
eval (ZipWith f xs ys) = zipWith f (eval xs) (eval ys)

export
uncons : VE (S n) a -> (a, VE n a)
uncons (Lit (x :: xs)) = (x, Lit xs)
uncons (Repeat (S n) x) = (x, Repeat n x)
uncons (ZipWith f xxs yys) =
  case uncons xxs of
    (x, xs) => case uncons yys of
      (y, ys) => (f x y, ZipWith f xs ys)

export
vec : {n : Nat} -> (how : VEable n a ty) => ty -> VE n a
vec {how = Vector} = Lit
vec {n} {how = Single} = Repeat n
