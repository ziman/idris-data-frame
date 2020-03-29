module DataFrame.Expr

import public DataFrame.Signature

%default total

data Expr : Sig -> Type -> Type where
  L : a -> Expr sig a
  V : (cn : String) -> InSig cn a sig => Expr sig a
  Map : (a -> b) -> Expr sig a -> Expr sig b
  Ap : Expr sig (a -> b) -> Expr sig a -> Expr sig b
