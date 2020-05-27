module DataFrame.DataFrame

import public DataFrame.Columns
import public DataFrame.Signature

public export
record DF (sig : Sig) where
  constructor MkDF
  {rowCount : Nat}
  columns : Columns rowCount sig

-- binops are infix 6
infix 7 ^.
export
(^.) :
    (df : DF sig)
    -> (cn : String)
    -> {auto pf : InSig cn a sig}
    -> Vect (rowCount df) a
(^.) df cn {pf} = extract (columns df) pf

export
fromRow : {sig : Sig} -> Row sig -> DF sig
fromRow = MkDF . singleton
