module DataFrame.DataFrame

import DataFrame.Columns
import public DataFrame.Signature

public export
record DF (sig : Sig) where
  constructor MkDF
  {rowCount : Nat}
  columns : Columns rowCount sig

infix 3 ^.
export
(^.) :
    (df : DF sig)
    -> (cn : String)
    -> {auto pf : InSig cn a sig}
    -> Vect (rowCount df) a
(^.) df cn {pf} = extract (columns df) pf
