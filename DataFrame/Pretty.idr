module DataFrame.Pretty

import public DataFrame.Core

public export
data MaybeShow : Type -> Type where
  YesShow : Show a -> MaybeShow a
  NoShow : MaybeShow a

public export
maybeShow : (ms : MaybeShow a) => a -> String
maybeShow {ms = YesShow _} x = show x
maybeShow {ms = NoShow} x = "(not showable)"

{-
Show (DF sig) where
  show (DF columns) = 
-}
