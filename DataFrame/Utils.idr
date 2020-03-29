module DataFrame.Utils

%default total

infix 3 <&>
public export
(<&>) : Functor f => f a -> (a -> b) -> f b
(<&>) x f = map f x

public export
mapLeft : (a -> a') -> Either a b -> Either a' b
mapLeft f (Left x) = Left (f x)
mapLeft f (Right x) = Right x

export
(Show a, Show b) => Show (Either a b) where
  show (Left x) = "(Left " ++ show x ++ ")"
  show (Right x) = "(Right " ++ show x ++ ")"
