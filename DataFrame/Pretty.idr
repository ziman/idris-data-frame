module DataFrame.Pretty

import Data.Nat
import Data.String
import DataFrame.Ops
import DataFrame.Columns
import public DataFrame.DataFrame

%default total

public export
data Alignment = Left | Right

public export
interface ShowDF a where
  showDF : a -> String
  alignment : Alignment

export
ShowDF Integer where
  showDF = show
  alignment = Right

export
ShowDF Double where
  showDF = show
  alignment = Right

export
ShowDF Int where
  showDF = show
  alignment = Right

export
ShowDF String where
  showDF = id
  alignment = Left

export
ShowDF Bool where
  showDF True = "yes"
  showDF False = "no"
  alignment = Left

export
ShowDF a => ShowDF (Maybe a) where
  showDF (Just x) = showDF x
  showDF Nothing = ""
  alignment = alignment {a=a}

toStringColumns : {sig : Sig} -> (sdfs : All ShowDF sig)
    => Columns n sig -> Vect (length sig) (Alignment, String, Vect n String)
toStringColumns {sig = []} [] = []
toStringColumns {sig = (cn :- a) :: sig} {sdfs = sdf :: _} (xs :: cols) =
  (alignment {a}, cn, map showDF xs) :: toStringColumns cols

pad : Alignment -> Nat -> Char -> String -> String
pad alignment width c str =
  case cmp (length str) width of
    CmpLT d => case alignment of
      Left => str ++ pack (replicate (S d) c)
      Right => pack (replicate (S d) c) ++ str
    _ => str

layout : Vect n Nat -> Vect n (Alignment, String, Vect m String) -> Vect n (Vect (2 + m) String)
layout [] [] = []
layout (width :: widths) ((al, cn, col) :: cols) =
  (pad al width ' ' cn :: pad al width '-' "" :: map (pad al width ' ') col)
  :: layout widths cols

-- show with full control
export
toString : {sig : Sig} -> All ShowDF sig => DF sig -> String
toString {sig} (MkDF {rowCount = rcnt} cols) =
    unlines . map (unwords . toList) . toList
      $ transpose (layout (map colWidth scols) scols)
  where
    scols : Vect (length sig) (Alignment, String, Vect rcnt String)
    scols = toStringColumns cols

    colWidth : (Alignment, String, Vect m String) -> Nat
    colWidth (al, cn, vals) = foldr max Z (length cn :: map length vals)

-- show with default options
export
{sig : Sig} -> All ShowDF sig => Show (DF sig) where
  show = toString . Ops.head 16
