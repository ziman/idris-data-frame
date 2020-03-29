module DataFrame.Vector

import public Data.Nat
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

public export
trueCount : Vect n Bool -> Nat
trueCount [] = 0
trueCount (True  :: xs) = S (trueCount xs)
trueCount (False :: xs) =    trueCount xs

infix 3 `where_`
export
where_ : Vect n a -> (mask : Vect n Bool) -> Vect (trueCount mask) a
where_ [] [] = []
where_ (x :: xs) (True :: mask) = x :: (xs `where_` mask)
where_ (x :: xs) (False :: mask) = xs `where_` mask

export
take : (m : Nat) -> Vect n a -> Vect (minimum m n) a
take Z xs = []
take (S m) [] = []
take (S m) (x :: xs) = x :: take m xs
