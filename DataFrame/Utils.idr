module DataFrame.Utils

%default total

infixl 3 <&>
public export
(<&>) : Functor f => f a -> (a -> b) -> f b
(<&>) x f = map f x

export
mapId : {xs : List a} -> map (\x => x) xs = xs
mapId {xs = []} = Refl
mapId {xs = x :: xs} = cong (x ::) mapId
