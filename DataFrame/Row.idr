module DataFrame.Row

import public DataFrame.Signature

%default total

public export
data Row : Sig -> Type where
  Nil : Row Nil
  (::) : a -> Row sig -> Row (cn :- a :: sig)
