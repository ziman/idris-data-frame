module DataFrame.Pretty

import DataFrame.Ops
import public DataFrame.Core

public export
data MaybeShow : Type -> Type where
  YesShow : Show a -> MaybeShow a
  NoShow : MaybeShow a

public export
maybeShow : (ms : MaybeShow a) => a -> String
maybeShow {ms = YesShow _} x = show x
maybeShow {ms = NoShow} x = "(not showable)"

export
toString : {sig : Sig} -> DF sig -> String
toString df = ?rhs

export
{sig : Sig} -> Show (DF sig) where
  show = toString . Ops.head 16
