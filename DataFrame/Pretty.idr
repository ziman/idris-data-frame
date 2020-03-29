module DataFrame.Pretty

import DataFrame.Ops
import public DataFrame.DataFrame

data MaybeShow : Type -> Type where
  YesShow : Show a -> MaybeShow a
  NoShow : MaybeShow a

maybeShow : (ms : MaybeShow a) => a -> String
maybeShow {ms = YesShow _} x = show x
maybeShow {ms = NoShow} x = "(not showable)"

toColumns : {sig : Sig} -> (mbShow : All MaybeShow sig)
    => Columns n sig -> List (String, Vect n String)
toColumns {sig = []} [] = []
toColumns {sig = cn :- a :: sig} {mbShow = _ :: _} (xs :: cols) =
  (cn, map maybeShow xs) :: toColumns cols

export
toString : {sig : Sig} -> All MaybeShow sig => DF sig -> String
toString (MkDF cols) = ?rhs

export
{sig : Sig} -> All MaybeShow sig => Show (DF sig) where
  show = toString . Ops.head 16
