module DataFrame.Pretty

import Data.Strings
import DataFrame.Ops
import public DataFrame.DataFrame

public export
data MaybeShow : Type -> Type where
  YesShow : Show a -> MaybeShow a
  NoShow : MaybeShow a

maybeShow : (ms : MaybeShow a) => a -> String
maybeShow {ms = YesShow _} x = show x
maybeShow {ms = NoShow} x = "(not showable)"

toStringColumns : {sig : Sig} -> (mbShow : All MaybeShow sig)
    => Columns n sig -> Vect (length sig) (String, Vect n String)
toStringColumns {sig = []} [] = []
toStringColumns {sig = cn :- a :: sig} {mbShow = _ :: _} (xs :: cols) =
  (cn, map maybeShow xs) :: toStringColumns cols

layout : Vect n Nat -> Vect n (String, Vect m String) -> Vect n (Vect (2 + m) String)
layout widths scols = ?rhs

export
toString : {sig : Sig} -> All MaybeShow sig => DF sig -> String
toString {sig} (MkDF {rowCount} cols) =
    unlines . map (unwords . toList) . toList
      $ transpose (layout widths scols)
  where
    scols : Vect (length sig) (String, Vect rowCount String)
    scols = toStringColumns cols

    widths : Vect (length sig) Nat
    widths = map (\(x,xs) => foldr max 0 (map Prelude.length $ x :: xs)) scols

export
{sig : Sig} -> All MaybeShow sig => Show (DF sig) where
  show = toString . Ops.head 16
