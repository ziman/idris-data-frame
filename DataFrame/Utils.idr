module DataFrame.Utils

%default total

export
mapId : {xs : List a} -> map (\x => x) xs = xs
mapId {xs = []} = Refl
mapId {xs = x :: xs} = cong (x ::) mapId
