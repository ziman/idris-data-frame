module DataFrame.Vector

import public Data.Vect

export
rep : {n : Nat} -> a -> Vect n a
rep {n} = replicate n

export
(||) : Vect n Bool -> Vect n Bool -> Vect n Bool
(||) = zipWith (\x, y => x || Delay y)

export
(&&) : Vect n Bool -> Vect n Bool -> Vect n Bool
(&&) = zipWith (\x, y => x && Delay y)

export
(==) : Eq a => Vect n a -> Vect n a -> Vect n Bool
(==) = zipWith (==)

export
(/=) : Eq a => Vect n a -> Vect n a -> Vect n Bool
(/=) = zipWith (/=)

export
(<) : Ord a => Vect n a -> Vect n a -> Vect n Bool
(<) = zipWith (<)

export
(<=) : Ord a => Vect n a -> Vect n a -> Vect n Bool
(<=) = zipWith (<=)

export
(>) : Ord a => Vect n a -> Vect n a -> Vect n Bool
(>) = zipWith (>)

export
(>=) : Ord a => Vect n a -> Vect n a -> Vect n Bool
(>=) = zipWith (>=)

public export
Op : (Type -> Type) -> Type
Op cls = {0 a : Type} -> {0 n : Nat} -> cls a => Vect n a -> Vect n a -> Vect n a

export
(+) : Op Num
(+) = zipWith (+)

export
(-) : Op Neg
(-) = zipWith (-)

export
(*) : Op Num
(*) = zipWith (*)

export
(/) : Op Fractional
(/) = zipWith (/)
