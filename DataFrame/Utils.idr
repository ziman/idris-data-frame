module DataFrame.Utils

%default total

infix 3 <&>
public export
(<&>) : Functor f => f a -> (a -> b) -> f b
(<&>) x f = map f x
